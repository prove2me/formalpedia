-- Prove2me | solution 1 for DiazModulus.fischler_prop_3_2_pencil
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-21T09:00:19.376329+00:00
-- url     : https://prove2.me/submissions/656724da-c955-42fa-ab25-9d5f8b0018ac

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_roy_rank_bound
import Theorems.Thm_DiazModulus_fischler_rational_hull

open Complex ComplexConjugate

/-! # Fischler 2001, Proposition 3.2 in pencil form

Let `M` be the `d × l` matrix whose columns are `F_a x`, with entries in `ℒ̃`. Roy's rank bound gives algebraic
invertible `P`, `Q` and sizes `d′ ≥ 1`, `l′ ≤ l` such that the block of `PMQ` with rows `< d′` and columns `≥ l′`
vanishes, and `(d − rk M)·l′ ≤ rk M·d′`. Take for `S` the span of the last `l − l′` columns of `Q`, and for `T` the
kernel of the first `d′` rows of `P`, so that `d − dim T = d′` and `l − dim S = l′`. For a column `s` of `Q` in `S`,
each of the first `d′` rows of `P · Σ s_a F_a` is an algebraic linear form vanishing at `x`, so it vanishes on the
smallest rational subspace containing `x`, which lies in the span of the algebraic vectors `w_b` of `x`'s rational
hull. Hence `(Σ s_a F_a) α ∈ T` for every `α` in that subspace, and linearity extends this to all of `S`. -/

namespace RC10_G2
open DiazModulus

theorem isRat_span {d : ℕ} (X : Set (Fin d → ℂ)) (hX : ∀ v ∈ X, ∀ i, v i ∈ Qbar) :
    Submodule.span ℂ {v : Fin d → ℂ | v ∈ Submodule.span ℂ X ∧ ∀ i, v i ∈ Qbar} = Submodule.span ℂ X :=
  le_antisymm (Submodule.span_le.mpr fun _ hv => hv.1)
    (Submodule.span_le.mpr fun v hv => Submodule.subset_span ⟨Submodule.subset_span hv, hX v hv⟩)

theorem pencil_mulVec {d l : ℕ} (F : Fin l → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ)
    (s : Fin l → ℂ) :
    (Matrix.of fun i a => ((F a).mulVec x) i).mulVec s = (∑ a, s a • F a).mulVec x := by
  ext k
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem pencil_sum_add {d l : ℕ} (F : Fin l → Matrix (Fin d) (Fin d) ℂ) (s s' : Fin l → ℂ) :
    (∑ a, (s + s') a • F a) = (∑ a, s a • F a) + ∑ a, s' a • F a := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by rw [Pi.add_apply, add_smul]

theorem pencil_sum_smul {d l : ℕ} (F : Fin l → Matrix (Fin d) (Fin d) ℂ) (c : ℂ) (s : Fin l → ℂ) :
    (∑ a, (c • s) a • F a) = c • ∑ a, s a • F a := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul]

end RC10_G2

open DiazModulus RC10_G2 in
theorem solution {d l : ℕ} (hd : 0 < d) (F : Fin l → Matrix (Fin d) (Fin d) ℂ)
    (hF : ∀ a i j, F a i j ∈ Qbar) (x : Fin d → ℂ) (hx : ∀ i, x i ∈ LogAlgTilde) :
    ∃ (S : Submodule ℂ (Fin l → ℂ)) (T : Submodule ℂ (Fin d → ℂ)),
      1 ≤ d - Module.finrank ℂ ↥T ∧
      (d - (Matrix.of fun i a => ((F a).mulVec x) i).rank) * (l - Module.finrank ℂ ↥S) ≤
        (Matrix.of fun i a => ((F a).mulVec x) i).rank * (d - Module.finrank ℂ ↥T) ∧
      ∀ s ∈ S, ∀ α ∈ sInf {E : Submodule ℂ (Fin d → ℂ) |
          Submodule.span ℂ {v : Fin d → ℂ | v ∈ E ∧ ∀ i, v i ∈ Qbar} = E ∧ x ∈ E},
        (∑ a, s a • F a).mulVec α ∈ T:= by
  classical
  set M : Matrix (Fin d) (Fin l) ℂ := Matrix.of fun i a => ((F a).mulVec x) i with hMdef
  have hM : ∀ i j, M i j ∈ LogAlgTilde := by
    intro i a
    show ∑ j, F a i j * x j ∈ LogAlgTilde
    exact LogAlgTilde.sum_mem fun j _ => LogAlgTilde.smul_mem (⟨F a i j, hF a i j⟩ : ↥Qbar) (hx j)
  obtain ⟨d', l', P, Q, hd'0, hd'd, hl', hP, hQ, hPa, hQa, hblock, hroy⟩ := roy_rank_bound M hM hd
  -- S
  let jU : Fin (l - l') → Fin l := fun t => ⟨l' + t.val, by omega⟩
  let fU : Fin (l - l') → Fin l → ℂ := fun t => fun q => Q q (jU t)
  have hfU : LinearIndependent ℂ fU := by
    have hQc : LinearIndependent ℂ Q.col :=
      Matrix.linearIndependent_cols_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det Q).mpr hQ)
    exact hQc.comp jU (fun t t' h => by
      simp only [jU, Fin.mk.injEq] at h; exact Fin.ext (by omega))
  -- T
  let iV : Fin d' → Fin d := fun s => ⟨s.val, by omega⟩
  let L : (Fin d → ℂ) →ₗ[ℂ] (Fin d' → ℂ) :=
    (LinearMap.funLeft ℂ ℂ iV) ∘ₗ P.mulVecLin
  have hLsurj : LinearMap.range L = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hPu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hP
    let z : Fin d → ℂ := fun i => if h : i.val < d' then y ⟨i.val, h⟩ else 0
    refine ⟨P⁻¹.mulVec z, ?_⟩
    ext s
    simp only [L, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply,
      LinearMap.funLeft_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP,
      Matrix.one_mulVec, z, iV, s.2, dite_true]
  have hT : Module.finrank ℂ ↥(LinearMap.ker L) + d' = d := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [hLsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  -- the rational hull of x
  obtain ⟨n, c, w, -, -, -, hwQ, hxw, hvan⟩ := fischler_rational_hull x
  have hle : sInf {E : Submodule ℂ (Fin d → ℂ) |
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ E ∧ ∀ i, v i ∈ Qbar} = E ∧ x ∈ E} ≤
      Submodule.span ℂ (Set.range w) := by
    refine sInf_le ⟨isRat_span _ ?_, ?_⟩
    · rintro _ ⟨b, rfl⟩ i; exact hwQ b i
    · rw [hxw]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  -- generators
  have hgen : ∀ t b, (∑ a, fU t a • F a).mulVec (w b) ∈ LinearMap.ker L := by
    intro t b
    rw [LinearMap.mem_ker]
    ext s
    set G := ∑ a, fU t a • F a with hG
    have hGQ : ∀ i j, G i j ∈ Qbar := by
      intro i j
      rw [hG, Matrix.sum_apply]
      exact Qbar.sum_mem fun a _ => by
        rw [Matrix.smul_apply, smul_eq_mul]; exact Qbar.mul_mem (hQa _ _) (hF _ _ _)
    have hPG : ∀ j, (P * G) (iV s) j ∈ Qbar := fun j => by
      rw [Matrix.mul_apply]; exact Qbar.sum_mem fun k _ => Qbar.mul_mem (hPa _ _) (hGQ _ _)
    have h0 : (P * G) (iV s) ⬝ᵥ x = 0 := by
      have h := hblock (iV s) (jU t) s.2 (by simp [jU])
      have key : (P * M * Q) (iV s) (jU t) = ((P * M * Q).mulVec (Pi.single (jU t) 1)) (iV s) := by
        rw [Matrix.mulVec_single_one, Matrix.col_apply]
      rw [key, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one, hMdef,
        pencil_mulVec, Matrix.mulVec_mulVec] at h
      exact h
    have := hvan _ hPG h0 b
    simp only [L, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply,
      LinearMap.funLeft_apply, Matrix.mulVec_mulVec, Pi.zero_apply]
    exact this
  refine ⟨Submodule.span ℂ (Set.range fU), LinearMap.ker L, by omega, ?_, ?_⟩
  · rw [finrank_span_eq_card hfU, Fintype.card_fin]
    have hr : M.rank ≤ d := Matrix.rank_le_height M
    have h1 : l - (l - l') = l' := by omega
    rw [h1]
    have h2 : d - Module.finrank ℂ ↥(LinearMap.ker L) = d' := by omega
    rw [h2]
    zify [hr] at hroy ⊢
    nlinarith
  · intro s hs α hα
    replace hα := hle hα
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨t, rfl⟩ := hs
      induction hα using Submodule.span_induction with
      | mem v hv => obtain ⟨b, rfl⟩ := hv; exact hgen t b
      | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
      | add u v _ _ hu hv => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hu hv
      | smul c u _ hu => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hu
    | zero =>
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, Matrix.zero_mulVec]
      exact Submodule.zero_mem _
    | add u v _ _ hu hv =>
      rw [pencil_sum_add, Matrix.add_mulVec]; exact Submodule.add_mem _ hu hv
    | smul c u _ hu =>
      rw [pencil_sum_smul, Matrix.smul_mulVec]; exact Submodule.smul_mem _ c hu

