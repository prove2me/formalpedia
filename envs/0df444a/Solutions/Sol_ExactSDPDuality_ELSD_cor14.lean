-- Prove2me | solution 1 for ExactSDPDuality.ELSD.cor14
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:27:42.994146+00:00
-- url     : https://prove2.me/submissions/f0cbcf2d-a82a-4310-995d-41c8b78b4673

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix Pointwise

namespace ExactSDPDuality.ELSD

lemma aux_c14_frob_add_left {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ) :
    frob (A + B) C = frob A C + frob B C := by
  simp [frob, add_mul, Finset.sum_add_distrib]

lemma aux_c14_frob_smul_left {n : ℕ} (a : ℝ) (A C : Matrix (Fin n) (Fin n) ℝ) :
    frob (a • A) C = a * frob A C := by
  simp [frob, Finset.mul_sum, mul_assoc]

lemma aux_c14_frob_zero_left {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) :
    frob 0 C = 0 := by
  simp [frob]

lemma aux_c14_frob_comm {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℝ) :
    frob A C = frob C A := by
  simp [frob, mul_comm]

lemma aux_c14_frob_sub_right {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ) :
    frob A (B - C) = frob A B - frob A C := by
  simp [frob, mul_sub, Finset.sum_sub_distrib]

lemma aux_c14_frob_sum_left {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    frob (∑ i ∈ s, f i) C = ∑ i ∈ s, frob (f i) C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [aux_c14_frob_zero_left]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, aux_c14_frob_add_left, ih]

lemma aux_c14_frob_vecMulVec {n : ℕ} (v : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    frob (vecMulVec v v) M = v ⬝ᵥ (M *ᵥ v) := by
  simp only [frob, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma aux_c14_frob_nonneg {n : ℕ} {U M : Matrix (Fin n) (Fin n) ℝ} (hU : U.PosSemidef)
    (hM : M.PosSemidef) : 0 ≤ frob U M := by
  obtain ⟨k, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hU
  rw [aux_c14_frob_sum_left]
  refine Finset.sum_nonneg fun i _ => ?_
  have hs : star (v i) = v i := star_trivial _
  rw [hs, aux_c14_frob_vecMulVec]
  have := hM.dotProduct_mulVec_nonneg (v i)
  rwa [hs] at this

lemma aux_c14_dot_Qstar {n m : ℕ} (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (x : Fin m → ℝ) :
    x ⬝ᵥ Qstar Q U = frob U (Qhat Q x) := by
  rw [aux_c14_frob_comm, Qhat, aux_c14_frob_sum_left]
  simp only [dotProduct, Qstar, aux_c14_frob_smul_left]
  exact Finset.sum_congr rfl fun i _ => by rw [aux_c14_frob_comm]

lemma aux_c14_Qaff_herm {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm) (x : Fin m → ℝ) :
    (Qaff Q0 Q x).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [Qaff, Qhat, Matrix.transpose_sub, Matrix.transpose_sum, Matrix.transpose_smul]
  rw [hQ0.eq]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [(hQ i).eq]

lemma aux_c14_polar_closed {m : ℕ} (S : Set (Fin m → ℝ)) : IsClosed (polar S) := by
  have : polar S = ⋂ x ∈ S, {y : Fin m → ℝ | x ⬝ᵥ y ≤ 1} := by
    ext y; simp [polar]
  rw [this]
  exact isClosed_biInter fun x _ =>
    isClosed_le (continuous_const.dotProduct continuous_id) continuous_const

end ExactSDPDuality.ELSD

open ExactSDPDuality.ELSD

theorem solution {n m r : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm)
    (h0 : (0 : Fin m → ℝ) ∈ feasibleSet Q0 Q) (A : Matrix (Fin r) (Fin m) ℝ) :
    polar (feasibleSet Q0 Q ∩ {x | A *ᵥ x = 0}) =
      closure (algPolar Q0 Q + perp {x | A *ᵥ x = 0}) := by
  set T : Set (Fin m → ℝ) := {x | A *ᵥ x = 0} with hTdef
  have hQ0psd : Q0.PosSemidef := by
    have : Qaff Q0 Q 0 = Q0 := by simp [Qaff, Qhat]
    have h := h0
    simp only [feasibleSet, Set.mem_ofPred_eq, this] at h
    exact h
  apply Set.Subset.antisymm
  · intro y hy
    by_contra hyC
    have hconvG : Convex ℝ (algPolar Q0 Q) := by
      rintro _ ⟨U, hU, hU1, rfl⟩ _ ⟨V, hV, hV1, rfl⟩ a b ha hb hab
      refine ⟨a • U + b • V, (hU.smul ha).add (hV.smul hb), ?_, ?_⟩
      · rw [aux_c14_frob_add_left, aux_c14_frob_smul_left, aux_c14_frob_smul_left]
        nlinarith
      · funext i
        simp [Qstar, aux_c14_frob_add_left, aux_c14_frob_smul_left]
    have hconvP : Convex ℝ (perp T) := by
      intro z hz w hw a b ha hb hab x hx
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct, hz x hx, hw x hx]
      simp
    have hconv : Convex ℝ (closure (algPolar Q0 Q + perp T)) :=
      (hconvG.add hconvP).closure
    obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hconv isClosed_closure hyC
    set xv : Fin m → ℝ := fun i => f (fun j => if i = j then 1 else 0) with hxv
    have hf : ∀ z, f z = z ⬝ᵥ xv := by
      intro z
      have := LinearMap.pi_apply_eq_sum_univ (f : (Fin m → ℝ) →ₗ[ℝ] ℝ) z
      simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
      rw [this]
      rfl
    have h0G : (0 : Fin m → ℝ) ∈ algPolar Q0 Q := by
      refine ⟨0, PosSemidef.zero, by simp [aux_c14_frob_zero_left], ?_⟩
      funext i; simp [Qstar, aux_c14_frob_zero_left]
    have hGC : algPolar Q0 Q ⊆ closure (algPolar Q0 Q + perp T) := by
      intro z hz
      apply subset_closure
      have : z + 0 ∈ algPolar Q0 Q + perp T :=
        Set.add_mem_add hz (by intro x _; simp)
      simpa using this
    have hPC : perp T ⊆ closure (algPolar Q0 Q + perp T) := by
      intro z hz
      apply subset_closure
      have : 0 + z ∈ algPolar Q0 Q + perp T := Set.add_mem_add h0G hz
      simpa using this
    have hu : 0 < u := by
      have := hfu 0 (hGC h0G)
      simpa using this
    -- rows of A are annihilated by f
    have hrow : ∀ j, (fun k => A j k) ⬝ᵥ xv = 0 := by
      intro j
      have hmem : ∀ t : ℝ, t • (fun k => A j k) ∈ perp T := by
        intro t x hx
        rw [smul_dotProduct]
        have hx' : (A *ᵥ x) j = 0 := by
          have := congrFun (show A *ᵥ x = 0 from hx) j
          simpa using this
        simp only [mulVec] at hx'
        rw [hx']
        simp
      by_contra hne
      have := hfu _ (hPC (hmem (u / ((fun k => A j k) ⬝ᵥ xv))))
      rw [hf, smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hne] at this
      exact lt_irrefl _ this
    set x' : Fin m → ℝ := u⁻¹ • xv with hx'def
    have hx'T : A *ᵥ x' = 0 := by
      rw [hx'def, Matrix.mulVec_smul]
      have : A *ᵥ xv = 0 := by
        funext j
        simpa [mulVec] using hrow j
      rw [this, smul_zero]
    have hkey : ∀ U : Matrix (Fin n) (Fin n) ℝ, U.PosSemidef → frob U Q0 ≤ 1 →
        x' ⬝ᵥ Qstar Q U < 1 := by
      intro U hU hU1
      have hlt := hfu _ (hGC ⟨U, hU, hU1, rfl⟩)
      rw [hf, dotProduct_comm] at hlt
      rw [hx'def, smul_dotProduct, smul_eq_mul]
      have := mul_lt_mul_of_pos_left hlt (inv_pos.mpr hu)
      rwa [inv_mul_cancel₀ hu.ne'] at this
    have hx'G : x' ∈ feasibleSet Q0 Q := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (aux_c14_Qaff_herm Q0 Q hQ0 hQ x') fun v => ?_
      have hs : star v = v := star_trivial _
      rw [hs, Qaff, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
      have ha : 0 ≤ v ⬝ᵥ (Q0 *ᵥ v) := by
        have := hQ0psd.dotProduct_mulVec_nonneg v
        rwa [hs] at this
      by_contra hlt'
      have hlt := not_le.mp hlt'
      set a := v ⬝ᵥ (Q0 *ᵥ v)
      set b := v ⬝ᵥ (Qhat Q x' *ᵥ v)
      have hb : 0 < b := lt_of_le_of_lt ha hlt
      have hvv : (vecMulVec v v).PosSemidef := by
        have := posSemidef_vecMulVec_self_star v
        rwa [hs] at this
      have hU : (b⁻¹ • vecMulVec v v).PosSemidef := hvv.smul (inv_nonneg.mpr hb.le)
      have hU1 : frob (b⁻¹ • vecMulVec v v) Q0 ≤ 1 := by
        rw [aux_c14_frob_smul_left, aux_c14_frob_vecMulVec]
        rw [inv_mul_le_iff₀ hb]
        linarith
      have := hkey _ hU hU1
      rw [aux_c14_dot_Qstar, aux_c14_frob_smul_left, aux_c14_frob_vecMulVec,
        inv_mul_cancel₀ hb.ne'] at this
      exact lt_irrefl _ this
    have hle := hy x' ⟨hx'G, hx'T⟩
    have hgt : 1 < x' ⬝ᵥ y := by
      rw [hx'def, smul_dotProduct, smul_eq_mul, dotProduct_comm, ← hf]
      rw [lt_inv_mul_iff₀ hu]
      linarith
    linarith
  · apply closure_minimal _ (aux_c14_polar_closed _)
    rintro _ ⟨a, ⟨U, hU, hUQ0, rfl⟩, b, hb, rfl⟩ x ⟨hxG, hxT⟩
    rw [dotProduct_add]
    have hbx : x ⬝ᵥ b = 0 := by rw [dotProduct_comm]; exact hb x hxT
    rw [hbx, add_zero, aux_c14_dot_Qstar]
    have hnn := aux_c14_frob_nonneg hU hxG
    rw [Qaff, aux_c14_frob_sub_right] at hnn
    linarith
