-- Prove2me | solution 1 for Disjunctive.GeneralDisjunctions.lp_cut_equals_intersection_cut_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:35:19.674152+00:00
-- url     : https://prove2.me/submissions/d4813835-3a05-4867-b8d7-e903883ce499

import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Cglp_v2



namespace Disjunctive.GeneralDisjunctions

section LPC

variable {n : ℕ} {M T : Type*} [Fintype M] [Fintype T]

/-- homogeneous part of the CGLP constraints -/
def CglpHom (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (w : (Fin n → ℝ) × (T → M → ℝ) × (T → ℝ) × ℝ) : Prop :=
  (∀ t, w.1 = Matrix.vecMul (w.2.1 t) Atil + w.2.2.1 t • d t) ∧
    (∀ t, w.2.2.2 = dotProduct (w.2.1 t) btil + w.2.2.1 t * d0 t)

lemma cglpHom_comb (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (w e : (Fin n → ℝ) × (T → M → ℝ) × (T → ℝ) × ℝ) (a b : ℝ)
    (hw : CglpHom Atil btil d d0 w) (he : CglpHom Atil btil d d0 e) :
    CglpHom Atil btil d d0 (a • w + b • e) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, Matrix.add_vecMul, Matrix.smul_vecMul]
    rw [hw.1 t, he.1 t]
    simp only [smul_add, add_smul, smul_smul, smul_eq_mul]
    abel
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, add_dotProduct, smul_dotProduct]
    rw [hw.2 t, he.2 t]
    ring

variable [Nonempty T] [DecidableEq M]

lemma exists_zero_of_basic (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ)
    (d0 : T → ℝ) (α : Fin n → ℝ) (β : ℝ) (u : T → M → ℝ) (u0 : T → ℝ)
    (hbasic : IsBasicCGLP116Solution Atil btil d d0 α u u0 β)
    (hu0pos : ∀ t, 0 < u0 t) (k : M) : ∃ t, u t k = 0 := by
  by_contra hcon
  push_neg at hcon
  have hpos : ∀ t, 0 < u t k := fun t => lt_of_le_of_ne (hbasic.1.2.2.2.1 t k) (hcon t).symm
  set N : ℝ := (Fintype.card T : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set ε : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun t => u t k) with hε
  have hεpos : 0 < ε := by
    rw [hε, Finset.lt_inf'_iff]; intro t _; exact hpos t
  have hεle : ∀ t, ε ≤ u t k := fun t => Finset.inf'_le _ (Finset.mem_univ t)
  set δ : ℝ := min ε (1 / N) with hδ
  have hδpos : 0 < δ := lt_min hεpos (by positivity)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδN : δ * N ≤ 1 := by
    have : δ ≤ 1 / N := min_le_right _ _
    rw [le_div_iff₀ hNpos] at this; linarith
  set w : (Fin n → ℝ) × (T → M → ℝ) × (T → ℝ) × ℝ := (α, u, u0, β) with hw
  set e : (Fin n → ℝ) × (T → M → ℝ) × (T → ℝ) × ℝ :=
    (Atil k, fun _ i => if i = k then 1 else 0, fun _ => 0, btil k) with he
  have hfeas := hbasic.1
  have hwH : CglpHom Atil btil d d0 w := ⟨hfeas.1, hfeas.2.1⟩
  have heH : CglpHom Atil btil d d0 e := by
    refine ⟨fun t => ?_, fun t => ?_⟩
    · funext j
      simp [he, Matrix.vecMul, dotProduct]
    · simp [he, dotProduct]
  have hnorm : (∑ t, ((∑ i, u t i) + u0 t)) = 1 := hfeas.2.2.1
  have hsumE : (∑ t : T, ((∑ i : M, (if i = k then (1:ℝ) else 0)) + 0)) = N := by
    simp [hN]
  -- the two points
  have mem_of : ∀ s : ℝ, (∀ t i, 0 ≤ (1 - s * N) * u t i + s * (if i = k then 1 else 0)) →
      (∀ t, 0 ≤ (1 - s * N) * u0 t) →
      ((1 - s * N) • w + s • e) ∈ CGLP116FeasibleSet Atil btil d d0 := by
    intro s h1 h2
    have hH := cglpHom_comb Atil btil d d0 w e (1 - s * N) s hwH heH
    refine ⟨hH.1, hH.2, ?_, ?_, ?_⟩
    · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, hw, he]
      have : ∀ t : T, (∑ i, ((1 - s * N) * u t i + s * (if i = k then 1 else 0)))
          + ((1 - s * N) * u0 t + s * 0) =
          (1 - s * N) * ((∑ i, u t i) + u0 t) + s * ((∑ i : M, (if i = k then (1:ℝ) else 0)) + 0) := by
        intro t
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
      rw [Finset.sum_congr rfl (fun t _ => this t), Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hnorm, hsumE]
      ring
    · intro t i
      simpa [hw, he] using h1 t i
    · intro t
      simpa [hw, he] using h2 t
  have hp := mem_of δ (fun t i => by
      have := hfeas.2.2.2.1 t i
      have h0 : 0 ≤ 1 - δ * N := by linarith
      split_ifs <;> nlinarith) (fun t => by
      have := hfeas.2.2.2.2 t
      have h0 : 0 ≤ 1 - δ * N := by linarith
      nlinarith)
  have hq := mem_of (-δ) (fun t i => by
      have := hfeas.2.2.2.1 t i
      split_ifs with hik
      · subst hik
        have h1 := hεle t
        have h2 := mul_pos (mul_pos hδpos hNpos) (hpos t)
        nlinarith
      · have h3 : 0 ≤ (1 - -δ * N) * u t i :=
          mul_nonneg (by nlinarith [mul_pos hδpos hNpos]) this
        linarith) (fun t => by
      have := hfeas.2.2.2.2 t
      exact mul_nonneg (by nlinarith [mul_pos hδpos hNpos]) this)
  have hseg : w ∈ openSegment ℝ ((1 - δ * N) • w + δ • e) ((1 - -δ * N) • w + (-δ) • e) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have := hbasic.2 hp hq hseg
  have h2 := congrArg (fun z => z.2.2.1) this
  have h3 := congrFun h2 (Classical.arbitrary T)
  simp only [hw, he, Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul] at h3
  have hu := hu0pos (Classical.arbitrary T)
  nlinarith [mul_pos (mul_pos hδpos hNpos) hu]

end LPC

open Matrix in
theorem lpcut_core {n : ℕ} {M T : Type*} [Fintype M] [Fintype T]
    [Nonempty T] [DecidableEq M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (α : Fin n → ℝ) (β : ℝ) (u : T → M → ℝ) (u0 : T → ℝ)
    (hbasic : IsBasicCGLP116Solution Atil btil d d0 α u u0 β)
    (hu0pos : ∀ t, 0 < u0 t)
    (ι : Fin n → M) (hι_inj : Function.Injective ι)
    (hnonsing : IsUnit (Ahat Atil ι).det)
    (hsupp : ∀ t, ∀ i, i ∉ Finset.image ι Finset.univ → u t i = 0)
    (hint : BasicSolutionInIntS Atil btil ι d d0) :
    {x | β ≤ dotProduct α x} = IntersectionCutFromS Atil btil ι d d0 := by
  have hfeas := hbasic.1
  set A := Ahat Atil ι with hA
  set B := A⁻¹ with hB
  have hAB : A * B = 1 := Matrix.mul_nonsing_inv A hnonsing
  have hBA : B * A = 1 := Matrix.nonsing_inv_mul A hnonsing
  have sum_supp : ∀ g : M → ℝ, (∀ i ∉ Finset.image ι Finset.univ, g i = 0) →
      ∑ i, g i = ∑ j, g (ι j) := by
    intro g hg
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.image ι Finset.univ))
      (fun i _ hi => hg i hi), Finset.sum_image (fun a _ b _ h => hι_inj h)]
  set ut : T → Fin n → ℝ := fun t j => u t (ι j) with hut
  set bh : Fin n → ℝ := Bhat btil ι with hbh
  set abar0 : Fin n → ℝ := fun i => Abar0 Atil btil ι i with habar0
  have habar0' : abar0 = B *ᵥ bh := by funext i; rfl
  have hvm : ∀ t, Matrix.vecMul (u t) Atil = Matrix.vecMul (ut t) A := by
    intro t; funext k
    simp only [Matrix.vecMul, dotProduct, hA, Ahat, hut]
    exact sum_supp _ (fun i hi => by rw [hsupp t i hi, zero_mul])
  have hdb : ∀ t, dotProduct (u t) btil = dotProduct (ut t) bh := by
    intro t
    simp only [dotProduct, hbh, Bhat, hut]
    exact sum_supp _ (fun i hi => by rw [hsupp t i hi, zero_mul])
  have hα : ∀ t, α = Matrix.vecMul (ut t) A + u0 t • d t := by
    intro t; rw [← hvm t]; exact hfeas.1 t
  have hβ : ∀ t, β = dotProduct (ut t) bh + u0 t * d0 t := by
    intro t; rw [← hdb t]; exact hfeas.2.1 t
  set γ : Fin n → ℝ := Matrix.vecMul α B with hγ
  set c : ℝ := β - dotProduct α abar0 with hc
  have K1 : ∀ x, ∑ j, γ j * SurplusM Atil btil (ι j) x = dotProduct α x - dotProduct α abar0 := by
    intro x
    have : ∀ j, SurplusM Atil btil (ι j) x = (A *ᵥ x - bh) j := by
      intro j; simp [SurplusM, hA, Ahat, hbh, Bhat, Matrix.mulVec, dotProduct]
    simp_rw [this]
    change dotProduct γ (A *ᵥ x - bh) = _
    rw [dotProduct_sub, Matrix.dotProduct_mulVec, hγ, Matrix.vecMul_vecMul, hBA,
      Matrix.vecMul_one, habar0', Matrix.dotProduct_mulVec]
  have K2 : ∀ t, γ = ut t + u0 t • Matrix.vecMul (d t) B := by
    intro t
    rw [hγ, hα t, Matrix.add_vecMul, Matrix.vecMul_vecMul, hAB, Matrix.vecMul_one,
      Matrix.smul_vecMul]
  have K3 : ∀ t, c = u0 t * (d0 t - dotProduct (d t) abar0) := by
    intro t
    have e1 : dotProduct α abar0 = dotProduct (ut t) bh + u0 t * dotProduct (d t) abar0 := by
      rw [hα t, add_dotProduct, smul_dotProduct, smul_eq_mul, habar0',
        ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
    rw [hc, e1, hβ t]; ring
  have hcpos : 0 < c := by
    obtain t := Classical.arbitrary T
    rw [K3 t]
    exact mul_pos (hu0pos t) (by have := hint t; linarith)
  have K4 : ∀ t j, piT Atil btil ι d d0 t j =
      Matrix.vecMul (d t) B j / (d0 t - dotProduct (d t) abar0) := by
    intro t j
    simp only [piT, Abar, neg_neg, Matrix.vecMul, dotProduct, hB, hA, habar0]
  have hpi : ∀ j, piCoef Atil btil ι d d0 j = γ j / c := by
    intro j
    have hle : ∀ t, piT Atil btil ι d d0 t j ≤ γ j / c := by
      intro t
      rw [K4, K3 t, K2 t]
      have hδ : 0 < d0 t - dotProduct (d t) abar0 := by have := hint t; linarith
      have hut0 : 0 ≤ ut t j := hfeas.2.2.2.1 t (ι j)
      rw [div_le_div_iff₀ hδ (mul_pos (hu0pos t) hδ)]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [mul_nonneg hut0 hδ.le]
    obtain ⟨t0, ht0⟩ := exists_zero_of_basic Atil btil d d0 α β u u0 hbasic hu0pos (ι j)
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun t _ => hle t)
    · have : γ j / c = piT Atil btil ι d d0 t0 j := by
        rw [K4, K3 t0, K2 t0]
        have hδ : 0 < d0 t0 - dotProduct (d t0) abar0 := by have := hint t0; linarith
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hut, ht0, zero_add]
        field_simp [(hu0pos t0).ne']
      rw [this]
      exact Finset.le_sup' (fun t => piT Atil btil ι d d0 t j) (Finset.mem_univ t0)
  ext x
  simp only [Set.mem_setOf_eq, IntersectionCutFromS]
  have : ∑ j, piCoef Atil btil ι d d0 j * SurplusM Atil btil (ι j) x =
      (dotProduct α x - dotProduct α abar0) / c := by
    rw [← K1, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hpi]; ring
  rw [this, le_div_iff₀ hcpos, hc]
  constructor <;> intro h <;> linarith

end Disjunctive.GeneralDisjunctions

open Disjunctive.GeneralDisjunctions


theorem solution {n : ℕ} {M T : Type*} [Fintype M] [Fintype T]
    [Nonempty T] [DecidableEq M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (d : T → Fin n → ℝ) (d0 : T → ℝ)
    (α : Fin n → ℝ) (β : ℝ) (u : T → M → ℝ) (u0 : T → ℝ)
    (hbasic : IsBasicCGLP116Solution Atil btil d d0 α u u0 β)
    (hu0pos : ∀ t, 0 < u0 t)
    (ι : Fin n → M) (hι_inj : Function.Injective ι)
    (hnonsing : IsUnit (Ahat Atil ι).det)
    (hsupp : ∀ t, ∀ i, i ∉ Finset.image ι Finset.univ → u t i = 0)
    (hint : BasicSolutionInIntS Atil btil ι d d0) :
    {x | β ≤ dotProduct α x} = IntersectionCutFromS Atil btil ι d d0 := by
  exact lpcut_core Atil btil d d0 α β u u0 hbasic hu0pos ι hι_inj hnonsing hsupp hint
