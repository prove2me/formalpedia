-- Prove2me | solution 1 for DetDLP.lemma_5_2_degree_sensitive_contraction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:13:14.876086+00:00
-- url     : https://prove2.me/submissions/41153d42-30a3-4d87-be77-dfd463b150cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DetDLP_BTN
import Theorems.Thm_DetDLP_integer_coefficient_contraction_schedule
open Finset
namespace DetDLP.Coefficients

private noncomputable def lift {ℓ : ℕ} (a : Fin ℓ → ℕ) : Polynomial ℤ :=
  ∑ i, Polynomial.monomial i.val (a i : ℤ)

private noncomputable def project (P ℓ : ℕ) : Polynomial ℤ →+* TruncPoly P ℓ :=
  (Ideal.Quotient.mk _).comp (Polynomial.mapRingHom (Int.castRingHom (ZMod (2^P))))

private theorem project_lift (P ℓ : ℕ) (a : Fin ℓ → ℕ) :
    project P ℓ (lift a) = truncPolyOfCoeffs P ℓ a := by
  simp [project,lift,truncPolyOfCoeffs,Polynomial.map_monomial]

private theorem project_contract {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (G : BipartiteMultigraph) (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → R) :
    f (BTNContract G A) = BTNContract G (fun v t => f (A v t)) := by simp [BTNContract]

private theorem project_encode (P ℓ : ℕ) (Z : Polynomial ℤ) :
    EncodesTruncPoly P ℓ
      (encodeNatListBin (List.ofFn fun i : Fin ℓ => ((Z.coeff i.val : ZMod (2^P)).val)))
      (project P ℓ Z) := by
  let c (i : Fin ℓ) := (Z.coeff i.val : ZMod (2^P)).val
  refine ⟨c,fun i => ZMod.val_lt _,rfl,?_⟩
  unfold project truncPolyOfCoeffs
  apply Ideal.Quotient.eq.mpr
  rw [Ideal.mem_span_singleton,Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub,Polynomial.finsetSum_coeff,Polynomial.coe_mapRingHom,Polynomial.coeff_map]
  have hsum : (∑ i : Fin ℓ, (Polynomial.monomial i.val (c i : ZMod (2^P))).coeff d)
      = (c ⟨d,hd⟩ : ZMod (2^P)) := by
    rw [sum_eq_single (⟨d,hd⟩ : Fin ℓ)]
    · simp [Polynomial.coeff_monomial]
    · intro b _ hb
      have h : b.val ≠ d := fun e => hb (Fin.ext e)
      simp [Polynomial.coeff_monomial,h,Ne.symm h]
    · simp
  rw [hsum]
  simp [c]
end DetDLP.Coefficients

open Finset
namespace DetDLP.Schedule

private theorem mode_sum (β ρ : ℝ) (hβ : 0 ≤ β) (hρ : 0 < ρ) (D : ℕ) :
    (∑ i ∈ range D, (β/(8:ℝ)^i) / Real.sqrt (ρ/(2:ℝ)^i)) ≤ 2*(β/Real.sqrt ρ) := by
  have hr := Real.sqrt_pos.mpr hρ
  have ht (i : ℕ) : (β/(8:ℝ)^i)/Real.sqrt (ρ/(2:ℝ)^i) ≤ (β/Real.sqrt ρ)*(1/2:ℝ)^i := by
    have hi : 0 < Real.sqrt ((2:ℝ)^i) := Real.sqrt_pos.mpr (by positivity)
    have hs : Real.sqrt ((2:ℝ)^i) ≤ (4:ℝ)^i := by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨by positivity,?_⟩
      rw [pow_right_comm]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    calc
      _ = (β/Real.sqrt ρ)*(Real.sqrt ((2:ℝ)^i)/(8:ℝ)^i) := by
        rw [Real.sqrt_div hρ.le]; field_simp
      _ ≤ (β/Real.sqrt ρ)*((4:ℝ)^i/(8:ℝ)^i) := by gcongr
      _ = _ := by rw [← div_pow]; norm_num
  have geometric (k : ℕ) : (∑ i ∈ range k,(1/2:ℝ)^i) + 2*(1/2:ℝ)^k=2 := by
    induction k with
    | zero => norm_num
    | succ k ih => rw [sum_range_succ,pow_succ]; linarith
  calc
    _ ≤ ∑ i ∈ range D, (β/Real.sqrt ρ)*(1/2:ℝ)^i := sum_le_sum (fun i _ => ht i)
    _ = (β/Real.sqrt ρ)*(∑ i ∈ range D,(1/2:ℝ)^i) := (mul_sum ..).symm
    _ ≤ (β/Real.sqrt ρ)*2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [geometric D,pow_nonneg (by norm_num : 0 ≤ (1/2:ℝ)) D]
    _ = _ := mul_comm _ _

private theorem poly_mono {k K : ℕ} (hk : k ≤ K) (n : ℕ) : polyBound k n ≤ polyBound K n := by
  unfold polyBound
  apply mul_le_mul (by exact_mod_cast hk) (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) hk) (by positivity) (by positivity)

private theorem relax {M : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine}
    {o : Fin M.tapeCount} {input output : List Bool} {t s T S : ℝ}
    (h : RunsWithin M o input output t s) (ht : t ≤ T) (hs : s ≤ S) : RunsWithin M o input output T S := by
  obtain ⟨k,z,htrace,hhalt,hout,hk,hspace⟩ := h
  exact ⟨k,z,htrace,hhalt,hout,hk.trans ht,fun i c hi hc => (hspace i c hi hc).trans hs⟩
end DetDLP.Schedule

open DetDLP


open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem solution :
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P ℓ'),
            2 ≤ β →
            1 ≤ Told →
            G.nE ≤ C * β →
            G.nV ≤ β ^ c0 →
            1 ≤ P → P ≤ C * β →
            1 ≤ ℓ' → ℓ' ≤ C * β →
            BTNEntryEvaluable desc G P ℓ' T E outE (Told : ℝ) (((β + desc.length : ℕ) : ℝ) ^ c0) →
            let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
            let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
            ∃ w : List Bool,
              EncodesTruncPoly P ℓ' w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G β P ℓ') w
                (polyBound K (β + desc.length) * (Told : ℝ) *
                  (2 : ℝ) ^ ((K : ℝ) * (β : ℝ) / Real.sqrt (ρ : ℝ)))
                (polyBound K (β + desc.length)) := by
  classical
  intro C c0 hC hc E outE
  obtain ⟨M,out,k,hcore⟩ := integer_coefficient_contraction_schedule C c0 hC hc E outE
  refine ⟨M,out,3*k,?_⟩
  intro β P ℓ Told desc G T hβ ht he hv hp hp' hl hl' hE Δ ρ
  choose w henc hrun using hE
  choose a ha hw hT using henc
  let Z := BTNContract G (fun v t => Coefficients.lift (a v t))
  have hcanon : Coefficients.project P ℓ Z = BTNContract G T := by
    dsimp only [Z]
    rw [Coefficients.project_contract]
    congr 1
    funext v t
    rw [Coefficients.project_lift,← hT v t]
  refine ⟨_,hcanon ▸ Coefficients.project_encode P ℓ Z,?_⟩
  have hsteps := hcore β P ℓ Told desc G a hβ ht he hv hp hp' hl hl' ha
    (fun v t => (hw v t) ▸ hrun v t)
  let u := β+desc.length
  have hρ : 0 < (ρ : ℝ) := by
    exact_mod_cast (show 0 < ρ from lt_of_lt_of_le (by decide : 0<1) (le_max_left _ _))
  have hsum := Schedule.mode_sum β ρ (Nat.cast_nonneg _) hρ (ρ+1)
  have hpoly := Schedule.poly_mono (show k ≤ 3*k by omega) u
  apply Schedule.relax hsteps _ hpoly
  change polyBound k u*Told * (2 : ℝ)^((k : ℝ)*((β : ℝ)/Real.sqrt ρ+_)) ≤
    polyBound (3*k) u*Told*(2 : ℝ)^(((3*k : ℕ) : ℝ)*β/Real.sqrt ρ)
  have hexp : (k : ℝ)*((β : ℝ)/Real.sqrt ρ+ ∑ d ∈ range (ρ+1),
      ((β : ℝ)/(8:ℝ)^d)/Real.sqrt ((ρ : ℝ)/(2:ℝ)^d)) ≤
      ((3*k : ℕ) : ℝ)*β/Real.sqrt ρ := by
    push_cast
    rw [mul_div_assoc]
    nlinarith [mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α := ℝ) k)]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hpoly (Nat.cast_nonneg Told))
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by positivity)
    (by unfold polyBound; positivity)
