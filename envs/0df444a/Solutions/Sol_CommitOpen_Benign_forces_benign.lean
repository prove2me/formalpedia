-- Prove2me | solution 1 for CommitOpen.Benign.forces_benign
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:04:35.118254+00:00
-- url     : https://prove2.me/submissions/a888fd9b-ce9f-48fc-84ef-19ce83482d64

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign
open scoped ComplexOrder InnerProductSpace
open Matrix


noncomputable def ov (θ θ' b c : Bool) : ℂ := ∑ z : Bool, star (ketBit θ b z) * ketBit θ' c z

lemma sqrt2_inv_sq : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (1/2 : ℂ) := by
  have h : ((Real.sqrt 2 : ℂ)) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; simp
  have h0 : ((Real.sqrt 2 : ℂ)) ≠ 0 := by
    intro h'; rw [h'] at h; simp at h
  field_simp
  rw [← h]; ring

lemma ov_same (θ b c : Bool) : ov θ θ b c = if b = c then 1 else 0 := by
  have := sqrt2_inv_sq
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1/2 := by rw [sq]; exact this
  cases θ <;> cases b <;> cases c <;>
    simp [ov, ketBit, this] <;> norm_num

lemma ov_sq (θ θ' b c : Bool) : ‖ov θ θ' b c‖ ^ 2 ≤ if θ = θ' then 1 else 1 / 2 := by
  have hn : ‖((Real.sqrt 2 : ℂ)⁻¹)‖ ^ 2 = 1/2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (by norm_num)]; norm_num
  have := sqrt2_inv_sq
  cases θ <;> cases θ' <;> cases b <;> cases c <;>
    simp [ov, ketBit, hn, this] <;> norm_num [hn]

lemma ov_orth (θ θ' c c' : Bool) : ∑ b : Bool, star (ov θ θ' b c) * ov θ θ' b c' = if c = c' then 1 else 0 := by
  have := sqrt2_inv_sq
  have h2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = 1/2 := by rw [sq]; exact this
  cases θ <;> cases θ' <;> cases c <;> cases c' <;>
    simp [ov, ketBit, this] <;> norm_num


lemma prod_ov {m : ℕ} (θ θ' y z : Fin m → Bool) :
    ∑ a : Fin m → Bool, star (bb84Ket θ y a) * bb84Ket θ' z a = ∏ i, ov (θ i) (θ' i) (y i) (z i) := by
  have : ∀ a : Fin m → Bool, star (bb84Ket θ y a) * bb84Ket θ' z a
      = ∏ i, (star (ketBit (θ i) (y i) (a i)) * ketBit (θ' i) (z i) (a i)) := by
    intro a
    simp [bb84Ket, star_prod, Finset.prod_mul_distrib]
  simp_rw [this]
  unfold ov
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset Bool))
    (fun i b => star (ketBit (θ i) (y i) b) * ketBit (θ' i) (z i) b), Fintype.piFinset_univ]

lemma ket_orth {m : ℕ} (θ y z : Fin m → Bool) :
    ∑ a : Fin m → Bool, star (bb84Ket θ y a) * bb84Ket θ z a = if y = z then 1 else 0 := by
  rw [prod_ov]
  simp_rw [ov_same]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma ket_complete {m : ℕ} (θ : Fin m → Bool) (a a' : Fin m → Bool) :
    ∑ z : Fin m → Bool, bb84Ket θ z a * star (bb84Ket θ z a') = if a = a' then 1 else 0 := by
  classical
  set U : Matrix (Fin m → Bool) (Fin m → Bool) ℂ := Matrix.of fun z a => star (bb84Ket θ z a) with hU
  have h1 : U * Uᴴ = 1 := by
    ext z z'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hU, Matrix.of_apply, star_star,
      Matrix.one_apply]
    rw [ket_orth]
  have h2 : Uᴴ * U = 1 := by
    exact mul_eq_one_comm.mp h1
  have := congrFun (congrFun h2 a) a'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hU, Matrix.of_apply, star_star,
      Matrix.one_apply] at this
  rw [← this]



lemma psi_expand {m : ℕ} {E : Type} [Fintype E] (θ : Fin m → Bool)
    (ψ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (a : Fin m → Bool) (e : E) :
    ψ (a, e) = ∑ z : Fin m → Bool, bb84Ket θ z a * amp θ z ψ e := by
  unfold amp ampAlong
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ a' : Fin m → Bool, ∑ z : Fin m → Bool, bb84Ket θ z a * (star (bb84Ket θ z a') * ψ (a', e))
      = (if a = a' then 1 else 0) * ψ (a', e) := by
    intro a'
    rw [← ket_complete θ a a', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    ring
  simp_rw [this]
  simp

lemma amp_expand {m : ℕ} {E : Type} [Fintype E] (θs θh : Fin m → Bool)
    (ψ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (y : Fin m → Bool) (e : E) :
    amp θs y ψ e = ∑ z : Fin m → Bool, (∏ i, ov (θs i) (θh i) (y i) (z i)) * amp θh z ψ e := by
  conv_lhs => unfold amp ampAlong
  simp_rw [psi_expand θh ψ _ e, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [← prod_ov, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring


noncomputable def vecA {m : ℕ} {E : Type} (θ : Fin m → Bool) (c : (Fin m → Bool) → E → ℂ) :
    EuclideanSpace ℂ ((Fin m → Bool) × E) :=
  WithLp.toLp 2 fun p => ∑ y, bb84Ket θ y p.1 * c y p.2

lemma vecA_apply {m : ℕ} {E : Type} (θ : Fin m → Bool) (c : (Fin m → Bool) → E → ℂ) (a : Fin m → Bool) (e : E) :
    vecA θ c (a, e) = ∑ y, bb84Ket θ y a * c y e := rfl

lemma vecA_amp {m : ℕ} {E : Type} [Fintype E] (θ : Fin m → Bool) (c : (Fin m → Bool) → E → ℂ)
    (y' : Fin m → Bool) (e : E) : amp θ y' (vecA θ c) e = c y' e := by
  unfold amp ampAlong
  simp_rw [vecA_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ y : Fin m → Bool, ∑ a : Fin m → Bool, star (bb84Ket θ y' a) * (bb84Ket θ y a * c y e)
      = (if y' = y then 1 else 0) * c y e := by
    intro y
    rw [← ket_orth θ y' y, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [this]
  simp

lemma vecA_inner {m : ℕ} {E : Type} [Fintype E] (θ : Fin m → Bool) (c0 c : (Fin m → Bool) → E → ℂ) :
    ∑ p : (Fin m → Bool) × E, star (vecA θ c0 p) * vecA θ c p =
      ∑ y, ∑ e, star (c0 y e) * c y e := by
  have key : ∀ e : E, ∑ a : Fin m → Bool, star (vecA θ c0 (a, e)) * vecA θ c (a, e) =
      ∑ y, star (c0 y e) * c y e := by
    intro e
    have h1 : ∀ a : Fin m → Bool, star (vecA θ c0 (a, e)) * vecA θ c (a, e) =
        ∑ y, ∑ y', (star (bb84Ket θ y a) * bb84Ket θ y' a) * (star (c0 y e) * c y' e) := by
      intro a
      simp_rw [vecA_apply, star_sum, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro y' _
      simp only [star_mul']
      ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ket_orth]
    simp
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [key]
  rw [Finset.sum_comm]

lemma psi_eq_vecA {m : ℕ} {E : Type} [Fintype E] (θ : Fin m → Bool)
    (ψ : EuclideanSpace ℂ ((Fin m → Bool) × E)) :
    ψ = vecA θ (fun y e => amp θ y ψ e) := by
  ext ⟨a, e⟩
  rw [psi_expand θ ψ a e]
  rfl

lemma sum_star_self {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    ∑ p, star (v p) * v p = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  apply Finset.sum_congr rfl
  intro p _
  rw [Complex.star_def, Complex.conj_mul']

lemma norm_sq_vecA {m : ℕ} {E : Type} [Fintype E] (θ : Fin m → Bool) (c : (Fin m → Bool) → E → ℂ) :
    ‖vecA θ c‖ ^ 2 = ∑ y, ∑ e, ‖c y e‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← sum_star_self, vecA_inner]
  push_cast
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro e _
  rw [Complex.star_def, Complex.conj_mul']

/-- squared mass of the `y`-th coefficient -/
noncomputable def nmass {m : ℕ} {E : Type} [Fintype E] (θ : Fin m → Bool)
    (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (y : Fin m → Bool) : ℝ :=
  ∑ e, ‖amp θ y φ e‖ ^ 2

lemma nmass_nonneg {m : ℕ} {E : Type} [Fintype E] (θ : Fin m → Bool)
    (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (y : Fin m → Bool) : 0 ≤ nmass θ φ y :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma nmass_sum {m : ℕ} {E : Type} [Fintype E] (θ : Fin m → Bool)
    (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (hφ : ‖φ‖ = 1) : ∑ y, nmass θ φ y = 1 := by
  have h := norm_sq_vecA θ (fun y e => amp θ y φ e)
  rw [← psi_eq_vecA θ φ, hφ] at h
  simpa [nmass] using h.symm

lemma sum_ite_cut {m : ℕ} {E : Type} [Fintype E] (G : Finset (Fin m → Bool))
    (f : (Fin m → Bool) → E → ℝ) :
    ∑ y, ∑ e, (if y ∈ G then f y e else (0:ℝ)) = ∑ y ∈ G, ∑ e, f y e := by
  classical
  calc ∑ y, ∑ e, (if y ∈ G then f y e else (0:ℝ))
      = ∑ y, (if y ∈ G then ∑ e, f y e else 0) := by
        apply Finset.sum_congr rfl
        intro y _
        split_ifs <;> simp
    _ = _ := by rw [Finset.sum_ite_mem]; simp

lemma exists_proj {m : ℕ} {E : Type} [Fintype E] (θ : Fin m → Bool) (xh : Fin m → Bool)
    (G : Finset (Fin m → Bool)) (hxh : xh ∈ G)
    (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (hφ : ‖φ‖ = 1) :
    ∃ ψ : EuclideanSpace ℂ ((Fin m → Bool) × E), ‖ψ‖ = 1 ∧ (∀ y, y ∉ G → amp θ y ψ = 0) ∧
      1 - ‖∑ p, star (φ p) * ψ p‖ ^ 2 ≤ ∑ y ∈ Gᶜ, nmass θ φ y := by
  classical
  have hsum := nmass_sum θ φ hφ
  have hsplit : ∑ y ∈ G, nmass θ φ y + ∑ y ∈ Gᶜ, nmass θ φ y = 1 := by
    rw [Finset.sum_add_sum_compl]; exact hsum
  set g := ∑ y ∈ G, nmass θ φ y with hg
  have hg0 : 0 ≤ g := Finset.sum_nonneg (fun y _ => nmass_nonneg θ φ y)
  by_cases hgpos : 0 < g
  · set c : (Fin m → Bool) → E → ℂ := fun y e =>
      ((1 / Real.sqrt g : ℝ) : ℂ) * (if y ∈ G then amp θ y φ e else 0) with hc
    have h1 : ∀ y e, ‖c y e‖ ^ 2 = if y ∈ G then (1 / g) * ‖amp θ y φ e‖ ^ 2 else 0 := by
      intro y e
      simp only [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      split_ifs
      · rw [mul_pow, sq_abs, div_pow, Real.sq_sqrt hg0]; simp
      · simp
    have hnorm : ‖vecA θ c‖ ^ 2 = 1 := by
      rw [norm_sq_vecA]
      simp_rw [h1]
      rw [sum_ite_cut G (fun y e => (1 / g) * ‖amp θ y φ e‖ ^ 2)]
      simp_rw [← Finset.mul_sum]
      have : ∑ y ∈ G, ∑ e, ‖amp θ y φ e‖ ^ 2 = g := rfl
      rw [this]
      field_simp
    refine ⟨vecA θ c, ?_, ?_, ?_⟩
    · have := hnorm
      nlinarith [norm_nonneg (vecA θ c)]
    · intro y hy
      funext e
      rw [vecA_amp]
      simp [hc, hy]
    · have hφ' : ∀ p, φ p = vecA θ (fun y e => amp θ y φ e) p := fun p => by
        rw [← psi_eq_vecA θ φ]
      have hin : ∑ p, star (φ p) * vecA θ c p = ((Real.sqrt g : ℝ) : ℂ) := by
        simp_rw [hφ']
        rw [vecA_inner]
        have h2 : ∀ y e, star (amp θ y φ e) * c y e =
            if y ∈ G then (((1 / Real.sqrt g : ℝ) : ℂ)) * ((‖amp θ y φ e‖ ^ 2 : ℝ) : ℂ) else 0 := by
          intro y e
          simp only [hc]
          split_ifs
          · rw [Complex.star_def]
            have := Complex.conj_mul' (amp θ y φ e)
            push_cast
            rw [mul_left_comm, this]
          · simp
        simp_rw [h2]
        have h3 : ∀ y : Fin m → Bool, ∑ e, (if y ∈ G then (((1 / Real.sqrt g : ℝ) : ℂ)) * ((‖amp θ y φ e‖ ^ 2 : ℝ) : ℂ) else 0)
            = if y ∈ G then (((1 / Real.sqrt g : ℝ) : ℂ)) * ((nmass θ φ y : ℝ) : ℂ) else 0 := by
          intro y
          split_ifs
          · rw [← Finset.mul_sum]; unfold nmass; push_cast; rfl
          · simp
        simp_rw [h3]
        rw [Finset.sum_ite_mem]
        simp only [Finset.univ_inter]
        rw [← Finset.mul_sum]
        have hsq := Real.sq_sqrt hg0
        have hsp : 0 < Real.sqrt g := Real.sqrt_pos.mpr hgpos
        rw [← Complex.ofReal_sum, ← hg]
        rw [← Complex.ofReal_mul]
        congr 1
        field_simp
        nlinarith
      rw [hin, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hg0]
      linarith
  · have hg00 : g = 0 := le_antisymm (not_lt.mp hgpos) hg0
    have hE : Nonempty E := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have : IsEmpty ((Fin m → Bool) × E) := by
        constructor
        intro p
        exact hne.false p.2
      have h0 : φ = 0 := Subsingleton.elim _ _
      rw [h0] at hφ
      simp at hφ
    obtain ⟨e0⟩ := hE
    set c : (Fin m → Bool) → E → ℂ := fun y e => if y = xh ∧ e = e0 then 1 else 0 with hc
    have hnorm : ‖vecA θ c‖ ^ 2 = 1 := by
      rw [norm_sq_vecA]
      rw [Finset.sum_eq_single xh]
      · rw [Finset.sum_eq_single e0]
        · simp [hc]
        · intro e _ he; simp [hc, he]
        · simp
      · intro y _ hy
        apply Finset.sum_eq_zero
        intro e _
        simp [hc, hy]
      · simp
    refine ⟨vecA θ c, ?_, ?_, ?_⟩
    · nlinarith [norm_nonneg (vecA θ c)]
    · intro y hy
      funext e
      rw [vecA_amp]
      have : y ≠ xh := fun h => hy (h ▸ hxh)
      simp [hc, this]
    · have : ∑ y ∈ Gᶜ, nmass θ φ y = 1 := by linarith
      rw [this]
      linarith [sq_nonneg ‖∑ p, star (φ p) * vecA θ c p‖]


section
open scoped MatrixOrder
theorem traceNorm_le_rank {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) :
    WildeQIT.traceNorm M ≤ Real.sqrt (M.rank * (Matrix.trace (Mᴴ * M)).re) := by
  have hQ : (Mᴴ * M).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hH := hQ.isHermitian
  have h0 : 0 ≤ Mᴴ * M := Matrix.nonneg_iff_posSemidef.mpr hQ
  have hs : CFC.sqrt (Mᴴ * M) = hH.cfc Real.sqrt := by
    rw [CFC.sqrt_eq_real_sqrt _ h0, cfcₙ_eq_cfc, Matrix.IsHermitian.cfc_eq]
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := hQ.eigenvalues_nonneg
  have htr : (Matrix.trace (CFC.sqrt (Mᴴ * M))).re = ∑ i, Real.sqrt (hH.eigenvalues i) := by
    rw [hs]
    unfold Matrix.IsHermitian.cfc
    rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
    simp [Matrix.trace_diagonal]
  have htr2 : (Matrix.trace (Mᴴ * M)).re = ∑ i, hH.eigenvalues i := by
    rw [hH.trace_eq_sum_eigenvalues]; simp
  have hrank : (Mᴴ * M).rank = M.rank := Matrix.rank_conjTranspose_mul_self M
  have hr := hH.rank_eq_card_non_zero_eigs
  unfold WildeQIT.traceNorm
  rw [htr]
  rw [htr2, ← hrank, hr]
  set s : Finset n := Finset.univ.filter (fun i => hH.eigenvalues i ≠ 0) with hsdef
  have hcard : (Fintype.card {i // hH.eigenvalues i ≠ 0} : ℝ) = s.card := by
    rw [Fintype.card_subtype]
  rw [hcard]
  have h1 : ∑ i, Real.sqrt (hH.eigenvalues i) = ∑ i ∈ s, Real.sqrt (hH.eigenvalues i) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have : hH.eigenvalues i = 0 := by simpa [hsdef] using hi
    simp [this]
  have h2 : ∑ i, hH.eigenvalues i = ∑ i ∈ s, hH.eigenvalues i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have : hH.eigenvalues i = 0 := by simpa [hsdef] using hi
    simp [this]
  rw [h1, h2]
  apply Real.le_sqrt_of_sq_le
  have := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun i => Real.sqrt (hH.eigenvalues i))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at this
  calc _ ≤ _ := this
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.sq_sqrt (hnn i)]

end
lemma sq_diff_rank_one {ι : Type} [Fintype ι] (u v : ι → ℂ) :
    ∑ a, ∑ a', ‖u a * star (u a') - v a * star (v a')‖ ^ 2 =
      (∑ a, ‖u a‖ ^ 2) ^ 2 + (∑ a, ‖v a‖ ^ 2) ^ 2 - 2 * ‖∑ a, star (u a) * v a‖ ^ 2 := by
  have h1 : ∀ a a', ‖u a * star (u a') - v a * star (v a')‖ ^ 2 =
      ‖u a‖ ^ 2 * ‖u a'‖ ^ 2 + ‖v a‖ ^ 2 * ‖v a'‖ ^ 2
        - 2 * ((u a * star (v a)) * (star (u a') * v a')).re := by
    intro a a'
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_sub]
    simp only [Complex.star_def, map_mul, Complex.conj_conj, Complex.normSq_mul, Complex.normSq_conj]
    have : u a * (starRingEnd ℂ) (u a') * ((starRingEnd ℂ) (v a) * v a') =
        u a * (starRingEnd ℂ) (v a) * ((starRingEnd ℂ) (u a') * v a') := by ring
    rw [this]
  simp_rw [h1]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have h2 : ∑ i, ∑ i_1, (u i * star (v i) * (star (u i_1) * v i_1)).re
      = ‖∑ a, star (u a) * v a‖ ^ 2 := by
    have : ∑ i, ∑ i_1, u i * star (v i) * (star (u i_1) * v i_1)
        = (∑ a, u a * star (v a)) * (∑ a, star (u a) * v a) := by
      rw [Finset.sum_mul_sum]
    have h3 : (∑ a, u a * star (v a)) = star (∑ a, star (u a) * v a) := by
      simp [star_sum]
    have h4 : ∑ i, ∑ i_1, (u i * star (v i) * (star (u i_1) * v i_1)).re
        = (∑ i, ∑ i_1, u i * star (v i) * (star (u i_1) * v i_1)).re := by
      simp [Complex.re_sum]
    rw [h4, this, h3, Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [h2]
  ring

lemma card_test (m k : ℕ) : Fintype.card (Test m k) = m.choose k * 2 ^ k := by
  classical
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter (fun p : Finset (Fin m) × Finset (Fin m) => p.1.card = k ∧ p.2 ⊆ p.1)).card
      = ((Finset.powersetCard k (Finset.univ : Finset (Fin m))).sigma (fun T => T.powerset)).card := by
    apply Finset.card_bij (fun p _ => (⟨p.1, p.2⟩ : Σ _ : Finset (Fin m), Finset (Fin m)))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [Finset.mem_sigma, Finset.mem_powersetCard, hp.1, hp.2]
    · intro p _ q _ h
      simpa [Prod.ext_iff] using h
    · intro b hb
      simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_powerset] at hb
      exact ⟨(b.1, b.2), by simp [hb.1.2, hb.2], rfl⟩
  rw [this, Finset.card_sigma]
  simp only [Finset.card_powerset]
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_powersetCard.mp hx).2])]
  simp [Finset.card_powersetCard]


lemma trace_re_eq {p q : Type} [Fintype p] [Fintype q] [DecidableEq q] (M : Matrix p q ℂ) :
    (Matrix.trace (Mᴴ * M)).re = ∑ a, ∑ b, ‖M a b‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast


lemma cq_entry {m k : ℕ} {ι : Type} (ψ : Test m k → EuclideanSpace ℂ ι) (φ : EuclideanSpace ℂ ι)
    (p q : Test m k × ι) :
    (cqState (fun _ : Test m k => φ) - cqState ψ) p q =
      if p.1 = q.1 then (testProb m k p.1 : ℂ) * (φ p.2 * star (φ q.2) - ψ p.1 p.2 * star (ψ p.1 q.2))
      else 0 := by
  simp only [Matrix.sub_apply, cqState, Matrix.of_apply, pureState]
  split_ifs with h
  · ring
  · simp

lemma cq_rank {m k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : Test m k → EuclideanSpace ℂ ι)
    (φ : EuclideanSpace ℂ ι) :
    (cqState (fun _ : Test m k => φ) - cqState ψ).rank ≤ 2 * Fintype.card (Test m k) := by
  classical
  set c : ℂ := ((((m.choose k : ℝ) * 2 ^ k)⁻¹ : ℝ) : ℂ) with hc
  set X : Matrix (Test m k × ι) (Test m k × Bool) ℂ :=
    Matrix.of fun p r => if p.1 = r.1 then (if r.2 then ψ p.1 p.2 else φ p.2) else 0 with hX
  set Y : Matrix (Test m k × Bool) (Test m k × ι) ℂ :=
    Matrix.of fun r q => (if r.2 then -c else c) * star (X q r) with hY
  have hD : cqState (fun _ : Test m k => φ) - cqState ψ = X * Y := by
    ext p q
    rw [cq_entry]
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, hX, hY, Matrix.of_apply]
    rw [Finset.sum_eq_single p.1]
    · simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
      by_cases h : p.1 = q.1
      · rw [if_pos h, ← h]
        simp only [testProb, hc, if_true]
        simp
        ring
      · rw [if_neg h]
        simp [Ne.symm h, h]
    · intro s _ hs
      simp [Ne.symm hs]
    · simp
  rw [hD]
  calc (X * Y).rank ≤ X.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Test m k × Bool) := Matrix.rank_le_card_width _
    _ = 2 * Fintype.card (Test m k) := by simp [Fintype.card_prod, mul_comm]


lemma cq_frob {m k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : Test m k → EuclideanSpace ℂ ι)
    (φ : EuclideanSpace ℂ ι) (hφ : ‖φ‖ = 1) (hψ : ∀ t, ‖ψ t‖ = 1) :
    (Matrix.trace ((cqState (fun _ : Test m k => φ) - cqState ψ)ᴴ *
        (cqState (fun _ : Test m k => φ) - cqState ψ))).re =
      (((m.choose k : ℝ) * 2 ^ k)⁻¹) ^ 2 *
        ∑ t, (2 - 2 * ‖∑ a, star (φ a) * ψ t a‖ ^ 2) := by
  classical
  rw [trace_re_eq]
  simp only [cq_entry, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have h1 : ∀ a : ι, ∑ t' : Test m k, ∑ a' : ι,
      ‖(if t = t' then (testProb m k t : ℂ) * (φ a * star (φ a') - ψ t a * star (ψ t a')) else 0)‖ ^ 2
      = ∑ a' : ι, (((m.choose k : ℝ) * 2 ^ k)⁻¹) ^ 2 * ‖φ a * star (φ a') - ψ t a * star (ψ t a')‖ ^ 2 := by
    intro a
    rw [Finset.sum_eq_single t]
    · apply Finset.sum_congr rfl
      intro a' _
      rw [if_pos rfl, norm_mul, mul_pow]
      simp [testProb]
    · intro t' _ ht'
      apply Finset.sum_eq_zero
      intro a' _
      simp [Ne.symm ht']
    · simp
  simp_rw [h1]
  simp_rw [← Finset.mul_sum]
  congr 1
  rw [sq_diff_rank_one]
  have e1 : ∑ a, ‖φ a‖ ^ 2 = 1 := by rw [← EuclideanSpace.norm_sq_eq, hφ]; norm_num
  have e2 : ∑ a, ‖ψ t a‖ ^ 2 = 1 := by rw [← EuclideanSpace.norm_sq_eq, hψ t]; norm_num
  rw [e1, e2]
  ring


theorem cq_trace_bound {m k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : Test m k → EuclideanSpace ℂ ι) (φ : EuclideanSpace ℂ ι) (hφ : ‖φ‖ = 1)
    (hψ : ∀ t, ‖ψ t‖ = 1) :
    traceDistance (cqState (fun _ : Test m k => φ)) (cqState ψ) ≤
      Real.sqrt (∑ t, testProb m k t * (1 - ‖∑ a, star (φ a) * ψ t a‖ ^ 2)) := by
  classical
  set D := cqState (fun _ : Test m k => φ) - cqState ψ with hD
  set c : ℝ := ((m.choose k : ℝ) * 2 ^ k)⁻¹ with hc
  set N : ℕ := Fintype.card (Test m k) with hN
  have hNc : (N : ℝ) = (m.choose k : ℝ) * 2 ^ k := by
    rw [hN, card_test]; push_cast; ring
  have hb := traceNorm_le_rank D
  rw [hD, cq_frob ψ φ hφ hψ] at hb
  have hr := cq_rank ψ φ
  have htr : 0 ≤ (Matrix.trace (Dᴴ * D)).re := by
    rw [trace_re_eq]
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [← hD] at hb
  have htr' := htr
  rw [hD, cq_frob ψ φ hφ hψ] at htr'
  have hX : WildeQIT.traceNorm D ≤ Real.sqrt (2 * N * (c ^ 2 * ∑ t, (2 - 2 * ‖∑ a, star (φ a) * ψ t a‖ ^ 2))) := by
    refine hb.trans (Real.sqrt_le_sqrt ?_)
    rw [hD, cq_frob ψ φ hφ hψ] at *
    apply mul_le_mul_of_nonneg_right _ htr'
    exact_mod_cast hr
  unfold traceDistance
  set S0 := ∑ t, (1 - ‖∑ a, star (φ a) * ψ t a‖ ^ 2) with hS0
  have hS : ∑ t, (2 - 2 * ‖∑ a, star (φ a) * ψ t a‖ ^ 2) = 2 * S0 := by
    rw [hS0, Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; ring
  rw [hS] at hX
  have hsum : ∑ t, testProb m k t * (1 - ‖∑ a, star (φ a) * ψ t a‖ ^ 2) = c * S0 := by
    rw [hS0, Finset.mul_sum]; rfl
  rw [hsum]
  by_cases hN0 : N = 0
  · have : 2 * (N:ℝ) * (c ^ 2 * (2 * S0)) = 0 := by rw [hN0]; simp
    rw [this, Real.sqrt_zero] at hX
    have hemp : IsEmpty (Test m k) := Fintype.card_eq_zero_iff.mp hN0
    have h0 : WildeQIT.traceNorm D = 0 := by
      unfold WildeQIT.traceNorm
      simp [Matrix.trace]
    rw [h0]
    simp [Real.sqrt_nonneg]
  · have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
    have hNc1 : (N : ℝ) * c = 1 := by
      rw [hNc] at hNpos
      have hch : (m.choose k : ℝ) ≠ 0 := by
        intro h; rw [h] at hNpos; simp at hNpos
      rw [hNc, hc]
      field_simp
    have hX0 : 0 ≤ 2 * (N:ℝ) * (c ^ 2 * (2 * S0)) := by
      rw [hS] at htr'
      exact mul_nonneg (by positivity) htr'
    apply le_trans (mul_le_mul_of_nonneg_left hX (by norm_num : (0:ℝ) ≤ 1/2))
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt hX0]
    have : 2 * (N:ℝ) * (c ^ 2 * (2 * S0)) = 4 * ((N * c) * (c * S0)) := by ring
    rw [this, hNc1]
    linarith


theorem lemma43_core {m k : ℕ} (ε : ℝ) (hε : 0 < ε) (xhat θhat : Fin m → Bool)
    (E : Type) [Fintype E] [DecidableEq E]
    (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (hφ : ‖φ‖ = 1) (B : ℝ)
    (hB : ∀ y : Fin m → Bool,
      ∑ t ∈ Finset.univ.filter (fun t : Test m k => y ∉ goodSet ε xhat t), testProb m k t ≤ B) :
    ∃ φt : Test m k → EuclideanSpace ℂ ((Fin m → Bool) × E),
      (∀ t, ‖φt t‖ = 1) ∧
      (∀ t y, y ∉ goodSet ε xhat t → amp θhat y (φt t) = 0) ∧
      traceDistance (cqState (fun _ : Test m k => φ)) (cqState φt) ≤ Real.sqrt B := by
  classical
  have hx : ∀ t : Test m k, xhat ∈ goodSet ε xhat t := by
    intro t
    simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 : ∀ S : Finset (Fin m), relHamming S xhat xhat = 0 := by
      intro S; simp [relHamming, hammingOn]
    rw [h1, h1]; linarith
  have hex := fun t : Test m k => exists_proj θhat xhat (goodSet ε xhat t) (hx t) φ hφ
  choose ψ hψ1 hψ2 hψ3 using hex
  refine ⟨ψ, hψ1, hψ2, ?_⟩
  refine (cq_trace_bound ψ φ hφ hψ1).trans (Real.sqrt_le_sqrt ?_)
  have hnm := nmass_sum θhat φ hφ
  calc ∑ t, testProb m k t * (1 - ‖∑ a, star (φ a) * ψ t a‖ ^ 2)
      ≤ ∑ t, testProb m k t * ∑ y ∈ (goodSet ε xhat t)ᶜ, nmass θhat φ y := by
        apply Finset.sum_le_sum
        intro t _
        exact mul_le_mul_of_nonneg_left (hψ3 t) (by unfold testProb; positivity)
    _ = ∑ y, nmass θhat φ y * ∑ t ∈ Finset.univ.filter (fun t : Test m k => y ∉ goodSet ε xhat t), testProb m k t := by
        have : ∀ t : Test m k, ∑ y ∈ (goodSet ε xhat t)ᶜ, nmass θhat φ y =
            ∑ y, if y ∉ goodSet ε xhat t then nmass θhat φ y else 0 := by
          intro t
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
          congr 1
          ext y; simp
        simp_rw [this, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> ring
    _ ≤ ∑ y, nmass θhat φ y * B := by
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left (hB y) (nmass_nonneg _ _ _)
    _ = B := by rw [← Finset.sum_mul, hnm, one_mul]


lemma ball_count {α : Type} [DecidableEq α] (U : Finset α) (μ : ℝ) (h0 : 0 < μ) (h1 : μ ≤ 1/2) :
    (((U.powerset).filter (fun S => (S.card : ℝ) ≤ μ * U.card)).card : ℝ)
      ≤ (2:ℝ) ^ (binEntropy2 μ * U.card) := by
  set n := U.card with hn
  set B := (U.powerset).filter (fun S => (S.card : ℝ) ≤ μ * n) with hB
  have hμ1 : μ < 1 := by linarith
  have h1μ : 0 < 1 - μ := by linarith
  have hsum : ∑ S ∈ U.powerset, μ ^ S.card * (1 - μ) ^ (n - S.card) = 1 := by
    rw [Finset.sum_pow_mul_eq_add_pow]; simp
  have hlow : ∀ S ∈ B, Real.exp (-(n * Real.binEntropy μ)) ≤ μ ^ S.card * (1 - μ) ^ (n - S.card) := by
    intro S hS
    rw [hB, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSU, hSc⟩ := hS
    have hle : S.card ≤ n := Finset.card_le_card hSU
    have hpos : 0 < μ ^ S.card * (1 - μ) ^ (n - S.card) := by positivity
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    rw [Real.binEntropy, Real.log_inv, Real.log_inv]
    have hcast : ((n - S.card : ℕ) : ℝ) = (n : ℝ) - S.card := by rw [Nat.cast_sub hle]
    rw [hcast]
    have hlog : Real.log μ ≤ Real.log (1 - μ) := Real.log_le_log h0 (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr hSc) (sub_nonneg.mpr hlog)]
  have hcount : (B.card : ℝ) * Real.exp (-(n * Real.binEntropy μ)) ≤ 1 := by
    calc (B.card : ℝ) * Real.exp (-(n * Real.binEntropy μ))
        = ∑ S ∈ B, Real.exp (-(n * Real.binEntropy μ)) := by simp
      _ ≤ ∑ S ∈ B, μ ^ S.card * (1 - μ) ^ (n - S.card) := Finset.sum_le_sum hlow
      _ ≤ ∑ S ∈ U.powerset, μ ^ S.card * (1 - μ) ^ (n - S.card) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro S _ _
          positivity
      _ = 1 := hsum
  have hexp : (2:ℝ) ^ (binEntropy2 μ * n) = Real.exp (n * Real.binEntropy μ) := by
    rw [Real.rpow_def_of_pos (by norm_num), binEntropy2]
    congr 1
    have : Real.log 2 ≠ 0 := by positivity
    field_simp
  rw [hexp]
  have hpe : 0 < Real.exp (n * Real.binEntropy μ) := Real.exp_pos _
  have : Real.exp (-(n * Real.binEntropy μ)) = (Real.exp (n * Real.binEntropy μ))⁻¹ := by
    rw [Real.exp_neg]
  rw [this] at hcount
  rw [← div_eq_mul_inv, div_le_one hpe] at hcount
  exact hcount

lemma J_card {m k : ℕ} (ε : ℝ) (hε : 0 < ε) (xhat x : Fin m → Bool) (t : Test m k)
    (herr : relHamming t.1.2 x xhat + ε ≤ 1 / 2) :
    (((goodSet ε xhat t ∩ agreeOn t.1.1 x).card : ℕ) : ℝ) ≤
      (2:ℝ) ^ (binEntropy2 (relHamming t.1.2 x xhat + ε) * (t.1.1ᶜ.card : ℝ)) := by
  classical
  set T := t.1.1 with hT
  set T' := t.1.2 with hT'
  have hsub : T' ⊆ T := t.2.2
  set r := relHamming T' x xhat with hr
  have hr0 : 0 ≤ r := by
    rw [hr]; unfold relHamming; positivity
  have hμ0 : 0 < r + ε := by linarith
  set D : (Fin m → Bool) → Finset (Fin m) := fun z => Tᶜ.filter (fun i => z i ≠ xhat i) with hD
  have hinj : Set.InjOn D ↑(goodSet ε xhat t ∩ agreeOn T x) := by
    intro z hz z' hz' hzz
    simp only [Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe, agreeOn, Finset.mem_filter,
      Finset.mem_univ, true_and] at hz hz'
    funext i
    by_cases hi : i ∈ T
    · rw [hz.2 i hi, hz'.2 i hi]
    · have : i ∈ D z ↔ i ∈ D z' := by rw [hzz]
      simp only [hD, Finset.mem_filter, Finset.mem_compl, hi, not_false_eq_true, true_and] at this
      by_contra hne
      cases h1 : z i <;> cases h2 : z' i <;> cases h3 : xhat i <;> simp_all
  have hmaps : ∀ z ∈ goodSet ε xhat t ∩ agreeOn T x,
      D z ∈ (Tᶜ.powerset).filter (fun S => (S.card : ℝ) ≤ (r + ε) * (Tᶜ.card : ℝ)) := by
    intro z hz
    rw [Finset.mem_inter, goodSet, Finset.mem_filter, agreeOn, Finset.mem_filter] at hz
    obtain ⟨⟨_, hg⟩, _, hagree⟩ := hz
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    have hr' : relHamming T' z xhat = r := by
      unfold relHamming hammingOn
      have : T'.filter (fun i => z i ≠ xhat i) = T'.filter (fun i => x i ≠ xhat i) := by
        apply Finset.filter_congr
        intro i hi
        rw [hagree i (hsub hi)]
      rw [this]; rfl
    rw [hr'] at hg
    by_cases hn : Tᶜ.card = 0
    · have : D z = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro i hi
        have : i ∈ Tᶜ := (Finset.mem_filter.mp hi).1
        rw [Finset.card_eq_zero] at hn
        simp [hn] at this
      rw [this, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hμ0.le (Nat.cast_nonneg _)
    · have hnpos : (0:ℝ) < Tᶜ.card := by exact_mod_cast Nat.pos_of_ne_zero hn
      unfold relHamming hammingOn at hg
      rw [div_le_iff₀ hnpos] at hg
      exact hg
  have hcard := Finset.card_le_card_of_injOn D hmaps hinj
  calc ((goodSet ε xhat t ∩ agreeOn T x).card : ℝ)
      ≤ (((Tᶜ.powerset).filter (fun S => (S.card : ℝ) ≤ (r + ε) * (Tᶜ.card : ℝ))).card : ℝ) := by
        exact_mod_cast hcard
    _ ≤ _ := ball_count Tᶜ (r + ε) hμ0 herr



lemma inner_self_C {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] (v : F) :
    ⟪v, v⟫_ℂ = ((‖v‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K v

lemma L1_sum {ι κ F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (Y : Finset ι) (W : Finset κ) [DecidableEq κ] (f : κ → F) (μ : ι → κ → ℂ)
    (horth : ∀ w ∈ W, ∀ w' ∈ W, ∑ y ∈ Y, star (μ y w) * μ y w' = if w = w' then 1 else 0) :
    ∑ y ∈ Y, ‖∑ w ∈ W, μ y w • f w‖ ^ 2 = ∑ w ∈ W, ‖f w‖ ^ 2 := by
  have h1 : ∀ y, ((‖∑ w ∈ W, μ y w • f w‖ : ℂ)) ^ 2 =
      ∑ w ∈ W, ∑ w' ∈ W, star (μ y w) * μ y w' * ⟪f w, f w'⟫_ℂ := by
    intro y
    rw [← inner_self_C, sum_inner]
    apply Finset.sum_congr rfl
    intro w _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro w' _
    rw [inner_smul_left, inner_smul_right]
    simp [mul_assoc]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ w ∈ W, ∑ y ∈ Y, ∑ w' ∈ W, star (μ y w) * μ y w' * ⟪f w, f w'⟫_ℂ
      = (‖f w‖ : ℂ) ^ 2 := by
    intro w hw
    rw [Finset.sum_comm]
    have : ∀ w' ∈ W, ∑ y ∈ Y, star (μ y w) * μ y w' * ⟪f w, f w'⟫_ℂ
        = (if w = w' then ⟪f w, f w'⟫_ℂ else 0) := by
      intro w' hw'
      rw [← Finset.sum_mul, horth w hw w' hw']
      split_ifs <;> simp
    rw [Finset.sum_congr rfl this]
    simp [hw, inner_self_C]
  exact Finset.sum_congr rfl h2


lemma L1_bound {ι κ F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (W : Finset κ) (f : κ → F) (μ : ι → κ → ℂ) (c : ℝ) (y : ι)
    (hb : ∀ w ∈ W, ‖μ y w‖ ^ 2 ≤ c) :
    ‖∑ w ∈ W, μ y w • f w‖ ^ 2 ≤ W.card * c * ∑ w ∈ W, ‖f w‖ ^ 2 := by
  have h1 : ‖∑ w ∈ W, μ y w • f w‖ ≤ ∑ w ∈ W, ‖μ y w‖ * ‖f w‖ := by
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro w _
    rw [norm_smul]
  have h2 : (∑ w ∈ W, ‖μ y w‖ * ‖f w‖) ^ 2 ≤ W.card * ∑ w ∈ W, (‖μ y w‖ * ‖f w‖) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : ∑ w ∈ W, (‖μ y w‖ * ‖f w‖) ^ 2 ≤ c * ∑ w ∈ W, ‖f w‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w hw
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (hb w hw) (sq_nonneg _)
  calc ‖∑ w ∈ W, μ y w • f w‖ ^ 2 ≤ (∑ w ∈ W, ‖μ y w‖ * ‖f w‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ W.card * ∑ w ∈ W, (‖μ y w‖ * ‖f w‖) ^ 2 := h2
    _ ≤ W.card * (c * ∑ w ∈ W, ‖f w‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
    _ = _ := by ring

noncomputable def muI {m : ℕ} (θ θhat : Fin m → Bool) (I : Finset (Fin m)) (y w : Fin m → Bool) : ℂ :=
  ∏ i ∈ I, ov (θ i) (θhat i) (y i) (w i)

lemma agreeOn_eq_piFinset {m : ℕ} (I : Finset (Fin m)) (x : Fin m → Bool) :
    agreeOn Iᶜ x = Fintype.piFinset (fun i => if i ∈ I then (Finset.univ : Finset Bool) else {x i}) := by
  ext y
  simp only [agreeOn, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
    Finset.mem_compl]
  constructor
  · intro h i
    by_cases hi : i ∈ I
    · simp [hi]
    · simp [hi, h i hi]
  · intro h i hi
    have := h i
    simpa [hi] using this

lemma muI_orth {m : ℕ} (θ θhat : Fin m → Bool) (I : Finset (Fin m)) (x w w' : Fin m → Bool)
    (hw : ∀ i, i ∉ I → w i = false) (hw' : ∀ i, i ∉ I → w' i = false) :
    ∑ y ∈ agreeOn Iᶜ x, star (muI θ θhat I y w) * muI θ θhat I y w' = if w = w' then 1 else 0 := by
  classical
  have h1 : ∀ y : Fin m → Bool, star (muI θ θhat I y w) * muI θ θhat I y w' =
      ∏ i, (if i ∈ I then star (ov (θ i) (θhat i) (y i) (w i)) * ov (θ i) (θhat i) (y i) (w' i) else 1) := by
    intro y
    unfold muI
    rw [star_prod, ← Finset.prod_mul_distrib]
    rw [Finset.prod_ite_mem Finset.univ I]
    simp
  simp_rw [h1]
  rw [agreeOn_eq_piFinset, ← Finset.prod_univ_sum (fun i => if i ∈ I then (Finset.univ : Finset Bool) else {x i})
    (fun i b => if i ∈ I then star (ov (θ i) (θhat i) b (w i)) * ov (θ i) (θhat i) b (w' i) else 1)]
  have h2 : ∀ i, ∑ b ∈ (if i ∈ I then (Finset.univ : Finset Bool) else {x i}),
      (if i ∈ I then star (ov (θ i) (θhat i) b (w i)) * ov (θ i) (θhat i) b (w' i) else 1)
      = if w i = w' i then 1 else 0 := by
    intro i
    by_cases hi : i ∈ I
    · simp only [hi, if_true]
      exact ov_orth _ _ _ _
    · simp [hi, hw i hi, hw' i hi]
  simp_rw [h2]
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma muI_sq {m : ℕ} (θ θhat : Fin m → Bool) (I : Finset (Fin m)) (y w : Fin m → Bool) :
    ‖muI θ θhat I y w‖ ^ 2 ≤ (1/2 : ℝ) ^ (hammingOn I θ θhat) := by
  unfold muI hammingOn
  rw [norm_prod, ← Finset.prod_pow]
  calc ∏ i ∈ I, ‖ov (θ i) (θhat i) (y i) (w i)‖ ^ 2
      ≤ ∏ i ∈ I, (if θ i = θhat i then (1:ℝ) else 1/2) := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i _; exact ov_sq _ _ _ _
    _ = _ := by
        rw [Finset.prod_ite]
        simp [Finset.filter_not]


noncomputable def piI {m : ℕ} (I : Finset (Fin m)) (z : Fin m → Bool) : Fin m → Bool :=
  fun i => if i ∈ I then z i else false

noncomputable def gam {m : ℕ} (θs θh : Fin m → Bool) (I : Finset (Fin m)) (x z : Fin m → Bool) : ℂ :=
  ∏ i ∈ Iᶜ, ov (θs i) (θh i) (x i) (z i)

lemma M_split {m : ℕ} (T I : Finset (Fin m)) (hI : I ⊆ Tᶜ) (θh θ x y z : Fin m → Bool)
    (hy : y ∈ agreeOn Iᶜ x) :
    ∏ i, ov (mixBasis T θh θ i) (θh i) (y i) (z i)
      = muI θ θh I y (piI I z) * gam (mixBasis T θh θ) θh I x z := by
  rw [← Finset.prod_mul_prod_compl I]
  congr 1
  · unfold muI
    apply Finset.prod_congr rfl
    intro i hi
    have hiT : i ∉ T := by simpa using hI hi
    simp [mixBasis, hiT, piI, hi]
  · unfold gam
    apply Finset.prod_congr rfl
    intro i hi
    have : y i = x i := by
      simp only [agreeOn, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact hy i hi
    rw [this]

lemma minent_core {m : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (θh θ x : Fin m → Bool) (T I : Finset (Fin m)) (hI : I ⊆ Tᶜ)
    (ψ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (J : Finset (Fin m → Bool))
    (hJ : ∀ z, amp θh z ψ ≠ 0 → (∀ i ∈ T, z i = x i) → z ∈ J) :
    ∀ y0 ∈ agreeOn Iᶜ x, outcomeProb (mixBasis T θh θ) ψ y0 ≤
      J.card * (1/2 : ℝ) ^ (hammingOn I θ θh) *
        ∑ y ∈ agreeOn Iᶜ x, outcomeProb (mixBasis T θh θ) ψ y := by
  classical
  set θs := mixBasis T θh θ with hθs
  let ev : (Fin m → Bool) → EuclideanSpace ℂ E := fun z => WithLp.toLp 2 (amp θh z ψ)
  have hStepA : ∀ y ∈ agreeOn Iᶜ x,
      (WithLp.toLp 2 (amp θs y ψ) : EuclideanSpace ℂ E) =
        ∑ z ∈ J, (∏ i, ov (θs i) (θh i) (y i) (z i)) • ev z := by
    intro y hy
    ext e'
    simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul]
    show amp θs y ψ e' = ∑ z ∈ J, (∏ i, ov (θs i) (θh i) (y i) (z i)) * amp θh z ψ e'
    rw [amp_expand θs θh ψ y e']
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro z _ hzJ
    by_cases h0 : amp θh z ψ e' = 0
    · rw [h0, mul_zero]
    · by_contra hne
      have hz1 : amp θh z ψ ≠ 0 := fun h => h0 (by rw [h]; rfl)
      have hnot : ¬ (∀ i ∈ T, z i = x i) := fun h => hzJ (hJ z hz1 h)
      simp only [not_forall] at hnot
      obtain ⟨i, hiT, hzi⟩ := hnot
      have hiI : i ∈ Iᶜ :=
        Finset.mem_compl.mpr (fun hiI => (Finset.mem_compl.mp (hI hiI)) hiT)
      have hyi : y i = x i := by
        simp only [agreeOn, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact hy i hiI
      have : ∏ i, ov (θs i) (θh i) (y i) (z i) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        have hθ : θs i = θh i := by simp [hθs, mixBasis, hiT]
        rw [hθ, ov_same, if_neg]
        rw [hyi]; exact fun h => hzi h.symm
      exact hne (by rw [this, zero_mul])
  have hStepB : ∀ y, outcomeProb θs ψ y = ‖(WithLp.toLp 2 (amp θs y ψ) : EuclideanSpace ℂ E)‖ ^ 2 := by
    intro y
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  -- grouping
  set W : Finset (Fin m → Bool) := J.image (piI I) with hW
  let f : (Fin m → Bool) → EuclideanSpace ℂ E := fun w =>
    ∑ z ∈ J.filter (fun z => piI I z = w), gam θs θh I x z • ev z
  have hStepC : ∀ y ∈ agreeOn Iᶜ x,
      (WithLp.toLp 2 (amp θs y ψ) : EuclideanSpace ℂ E) = ∑ w ∈ W, muI θ θh I y w • f w := by
    intro y hy
    rw [hStepA y hy]
    have h1 : ∀ z ∈ J, (∏ i, ov (θs i) (θh i) (y i) (z i)) • ev z
        = muI θ θh I y (piI I z) • (gam θs θh I x z • ev z) := by
      intro z _
      rw [M_split T I hI θh θ x y z hy, mul_smul]
    rw [Finset.sum_congr rfl h1]
    rw [← Finset.sum_fiberwise_of_maps_to (s := J) (t := W) (g := piI I)
      (fun z hz => Finset.mem_image_of_mem _ hz)]
    apply Finset.sum_congr rfl
    intro w _
    simp only [f]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [(Finset.mem_filter.mp hz).2]
  have hzero : ∀ w ∈ W, ∀ i, i ∉ I → w i = false := by
    intro w hw i hi
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hw
    simp [piI, hi]
  have horth : ∀ w ∈ W, ∀ w' ∈ W,
      ∑ y ∈ agreeOn Iᶜ x, star (muI θ θh I y w) * muI θ θh I y w' = if w = w' then 1 else 0 :=
    fun w hw w' hw' => muI_orth θ θh I x w w' (hzero w hw) (hzero w' hw')
  have hS := L1_sum (agreeOn Iᶜ x) W f (muI θ θh I) horth
  intro y0 hy0
  rw [hStepB y0, hStepC y0 hy0]
  have hsum : ∑ y ∈ agreeOn Iᶜ x, outcomeProb θs ψ y = ∑ w ∈ W, ‖f w‖ ^ 2 := by
    rw [← hS]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hStepB y, hStepC y hy]
  rw [hsum]
  have hb := L1_bound W f (muI θ θh I) ((1/2 : ℝ) ^ (hammingOn I θ θh)) y0
    (fun w _ => muI_sq θ θh I y0 w)
  refine hb.trans ?_
  have hWc : (W.card : ℝ) ≤ J.card := by
    exact_mod_cast Finset.card_image_le
  have hnn : 0 ≤ ∑ w ∈ W, ‖f w‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : (0:ℝ) ≤ (1/2 : ℝ) ^ (hammingOn I θ θh) := by positivity
  calc (W.card : ℝ) * (1 / 2 : ℝ) ^ hammingOn I θ θh * ∑ w ∈ W, ‖f w‖ ^ 2
      ≤ (J.card : ℝ) * (1 / 2 : ℝ) ^ hammingOn I θ θh * ∑ w ∈ W, ‖f w‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hnn
        exact mul_le_mul_of_nonneg_right hWc hc
    _ = _ := by rfl

lemma amp_restrict {m : ℕ} {E : Type} [Fintype E] (T : Finset (Fin m))
    (θh θ x : Fin m → Bool) (ψ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (J : Finset (Fin m → Bool))
    (hJ : ∀ z, amp θh z ψ ≠ 0 → (∀ i ∈ T, z i = x i) → z ∈ J)
    (y : Fin m → Bool) (hy : ∀ i ∈ T, y i = x i) (e' : E) :
    amp (mixBasis T θh θ) y ψ e' =
      ∑ z ∈ J, (∏ i, ov (mixBasis T θh θ i) (θh i) (y i) (z i)) * amp θh z ψ e' := by
  rw [amp_expand (mixBasis T θh θ) θh ψ y e']
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro z _ hzJ
  by_cases h0 : amp θh z ψ e' = 0
  · rw [h0, mul_zero]
  · by_contra hne
    have hz1 : amp θh z ψ ≠ 0 := fun h => h0 (by rw [h]; rfl)
    have hnot : ¬ (∀ i ∈ T, z i = x i) := fun h => hzJ (hJ z hz1 h)
    simp only [not_forall] at hnot
    obtain ⟨i, hiT, hzi⟩ := hnot
    have hyi : y i = x i := hy i hiT
    have : ∏ i, ov (mixBasis T θh θ i) (θh i) (y i) (z i) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have hθ : mixBasis T θh θ i = θh i := by simp [mixBasis, hiT]
      rw [hθ, ov_same, if_neg]
      rw [hyi]; exact fun h => hzi h.symm
    exact hne (by rw [this, zero_mul])

lemma bob_rank {m : ℕ} {E : Type} [Fintype E] [DecidableEq E] (T : Finset (Fin m))
    (θh θ x : Fin m → Bool) (ψ : EuclideanSpace ℂ ((Fin m → Bool) × E)) (J : Finset (Fin m → Bool))
    (hJ : ∀ z, amp θh z ψ ≠ 0 → (∀ i ∈ T, z i = x i) → z ∈ J) :
    (bobState (mixBasis T θh θ) ψ T x).rank ≤ J.card := by
  classical
  set A : Matrix E (agreeOn T x) ℂ := Matrix.of fun e y => amp (mixBasis T θh θ) y.1 ψ e with hA
  set B : Matrix E J ℂ := Matrix.of fun e z => amp θh z.1 ψ e with hB
  set C : Matrix J (agreeOn T x) ℂ :=
    Matrix.of fun z y => ∏ i, ov (mixBasis T θh θ i) (θh i) (y.1 i) (z.1 i) with hC
  have h1 : bobState (mixBasis T θh θ) ψ T x = A * Aᴴ := by
    ext e e'
    simp only [bobState, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, hA, Matrix.of_apply, Pi.star_apply]
    exact (Finset.sum_coe_sort (agreeOn T x) (fun y => amp (mixBasis T θh θ) y ψ e *
      star (amp (mixBasis T θh θ) y ψ e'))).symm
  have h2 : A = B * C := by
    ext e y
    simp only [hA, hB, hC, Matrix.of_apply, Matrix.mul_apply]
    have hy : ∀ i ∈ T, y.1 i = x i := by
      have := y.2
      simp only [agreeOn, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    rw [amp_restrict T θh θ x ψ J hJ y.1 hy e]
    rw [← Finset.sum_coe_sort J]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [h1]
  calc (A * Aᴴ).rank ≤ A.rank := Matrix.rank_mul_le_left _ _
    _ = (B * C).rank := by rw [h2]
    _ ≤ B.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card J := Matrix.rank_le_card_width _
    _ = J.card := Fintype.card_coe J

lemma binEntropy2_nonneg {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) : 0 ≤ binEntropy2 μ := by
  unfold binEntropy2
  exact div_nonneg (Real.binEntropy_nonneg h0 h1) (Real.log_nonneg (by norm_num))

theorem cor44_aux {m k : ℕ} {E : Type} [Fintype E] [DecidableEq E] (ε : ℝ) (hε : 0 < ε)
    (xhat θhat θ : Fin m → Bool) (t : Test m k)
    (φt : EuclideanSpace ℂ ((Fin m → Bool) × E)) (hunit : ‖φt‖ = 1)
    (hform : ∀ y, y ∉ goodSet ε xhat t → amp θhat y φt = 0)
    (x : Fin m → Bool) (herr : relHamming t.1.2 x xhat + ε ≤ 1 / 2)
    (hpos : 0 < ∑ y ∈ agreeOn t.1.1 x, outcomeProb (mixBasis t.1.1 θhat θ) φt y) :
    maxEntropy (bobState (mixBasis t.1.1 θhat θ) φt t.1.1 x) ≤
        binEntropy2 (relHamming t.1.2 x xhat + ε) * (t.1.1ᶜ.card : ℝ) ∧
      ∀ I : Finset (Fin m), I ⊆ t.1.1ᶜ →
        0 < ∑ y ∈ agreeOn Iᶜ x, outcomeProb (mixBasis t.1.1 θhat θ) φt y →
        (hammingOn I θ θhat : ℝ) - binEntropy2 (relHamming t.1.2 x xhat + ε) * (t.1.1ᶜ.card : ℝ) ≤
          condMinEntropy (outcomeProb (mixBasis t.1.1 θhat θ) φt) I x := by
  classical
  set T := t.1.1 with hT
  set H := binEntropy2 (relHamming t.1.2 x xhat + ε) with hH
  set J := goodSet ε xhat t ∩ agreeOn T x with hJdef
  have hr0 : 0 ≤ relHamming t.1.2 x xhat := by unfold relHamming; positivity
  have hH0 : 0 ≤ H := binEntropy2_nonneg (by linarith) (by linarith)
  have hJ : ∀ z, amp θhat z φt ≠ 0 → (∀ i ∈ T, z i = x i) → z ∈ J := by
    intro z hz hz2
    rw [hJdef, Finset.mem_inter]
    refine ⟨?_, ?_⟩
    · by_contra hn
      exact hz (hform z hn)
    · simpa [agreeOn] using hz2
  have hJcard := J_card ε hε xhat x t herr
  have hn0 : (0:ℝ) ≤ (Tᶜ.card : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, ?_⟩
  · have hrk := bob_rank T θhat θ x φt J hJ
    unfold maxEntropy
    by_cases hr : (bobState (mixBasis T θhat θ) φt T x).rank = 0
    · rw [hr]; simp; exact mul_nonneg hH0 hn0
    · have hrpos : (0:ℝ) < ((bobState (mixBasis T θhat θ) φt T x).rank : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hr
      calc Real.logb 2 ((bobState (mixBasis T θhat θ) φt T x).rank : ℝ)
          ≤ Real.logb 2 ((2:ℝ) ^ (H * (Tᶜ.card : ℝ))) := by
            apply Real.logb_le_logb_of_le (by norm_num) hrpos
            exact le_trans (by exact_mod_cast hrk) hJcard
        _ = H * (Tᶜ.card : ℝ) := Real.logb_rpow (by norm_num) (by norm_num)
  · intro I hI hposI
    set P := outcomeProb (mixBasis T θhat θ) φt with hP
    set S := ∑ y ∈ agreeOn Iᶜ x, P y with hS
    have hcore := minent_core θhat θ x T I hI φt J hJ
    have hbound : ∀ y ∈ agreeOn Iᶜ x, P y / S ≤ (2:ℝ) ^ (H * (Tᶜ.card : ℝ) - (hammingOn I θ θhat : ℝ)) := by
      intro y hy
      rw [div_le_iff₀ hposI]
      have h1 := hcore y hy
      have h2 : (J.card : ℝ) * (1/2 : ℝ) ^ (hammingOn I θ θhat) ≤
          (2:ℝ) ^ (H * (Tᶜ.card : ℝ) - (hammingOn I θ θhat : ℝ)) := by
        rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, one_div, inv_pow, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right hJcard (by positivity)
      calc P y ≤ (J.card : ℝ) * (1/2 : ℝ) ^ (hammingOn I θ θhat) * S := h1
        _ ≤ _ := mul_le_mul_of_nonneg_right h2 hposI.le
    obtain ⟨y1, hy1, hy1pos⟩ : ∃ y ∈ agreeOn Iᶜ x, 0 < P y := by
      by_contra hcon
      simp only [not_exists, not_and, not_lt] at hcon
      have : S ≤ 0 := Finset.sum_nonpos hcon
      linarith
    unfold condMinEntropy
    have hsup_pos : 0 < (agreeOn Iᶜ x).sup' ⟨x, self_mem_agreeOn Iᶜ x⟩ (fun y => P y / S) := by
      refine lt_of_lt_of_le ?_ (Finset.le_sup' (fun y => P y / S) hy1)
      exact div_pos hy1pos hposI
    have hsup_le : (agreeOn Iᶜ x).sup' ⟨x, self_mem_agreeOn Iᶜ x⟩ (fun y => P y / S)
        ≤ (2:ℝ) ^ (H * (Tᶜ.card : ℝ) - (hammingOn I θ θhat : ℝ)) :=
      Finset.sup'_le _ _ hbound
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hsup_pos hsup_le
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at this
    linarith



open scoped ComplexOrder


lemma mgf_step {L : Type} [Fintype L] (w : L → ℝ) (hw0 : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1)
    (g : L → ℝ) (hg : ∀ l, |g l| ≤ 1) (hg0 : ∑ l, w l * g l = 0) (lam : ℝ) (hlam : |lam| ≤ 1) :
    ∑ l, w l * Real.exp (lam * g l) ≤ Real.exp (lam ^ 2) := by
  have h1 : ∀ l, Real.exp (lam * g l) ≤ 1 + lam * g l + lam ^ 2 := by
    intro l
    have hx : |lam * g l| ≤ 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg lam, abs_nonneg (g l), hg l]
    have := Real.abs_exp_sub_one_sub_id_le hx
    have h2 : (lam * g l) ^ 2 ≤ lam ^ 2 := by
      rw [mul_pow]
      have : g l ^ 2 ≤ 1 := by
        have := hg l
        nlinarith [abs_nonneg (g l), sq_abs (g l)]
      nlinarith [sq_nonneg lam]
    have := (abs_le.mp this).2
    linarith
  calc ∑ l, w l * Real.exp (lam * g l) ≤ ∑ l, w l * (1 + lam * g l + lam ^ 2) :=
        Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (h1 l) (hw0 l))
    _ = 1 + lam ^ 2 := by
        have : ∀ l, w l * (1 + lam * g l + lam ^ 2) = w l * (1 + lam ^ 2) + lam * (w l * g l) := by
          intro l; ring
        simp_rw [this]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw1, ← Finset.mul_sum, hg0]
        ring
    _ ≤ Real.exp (lam ^ 2) := by
        have := Real.add_one_le_exp (lam ^ 2)
        linarith

lemma chernoff_gen {L : Type} [Fintype L] [DecidableEq L] {m : ℕ} (w : L → ℝ) (hw0 : ∀ l, 0 ≤ w l)
    (hw1 : ∑ l, w l = 1) (f : Fin m → L → ℝ)
    (hf : ∀ i l, |f i l - ∑ l', w l' * f i l'| ≤ 1) (lam : ℝ) (hlam : |lam| ≤ 1) (τ : ℝ) :
    ∑ ω ∈ Finset.univ.filter (fun ω : Fin m → L =>
        τ ≤ lam * (∑ i, f i (ω i) - ∑ i, ∑ l', w l' * f i l')),
      ∏ i, w (ω i) ≤ Real.exp (-τ + m * lam ^ 2) := by
  set μ : Fin m → ℝ := fun i => ∑ l', w l' * f i l' with hμ
  have hmgf : ∑ ω : Fin m → L, (∏ i, w (ω i)) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i))
      ≤ Real.exp (m * lam ^ 2) := by
    have h1 : ∀ ω : Fin m → L, (∏ i, w (ω i)) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i))
        = ∏ i, (w (ω i) * Real.exp (lam * (f i (ω i) - μ i))) := by
      intro ω
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    simp_rw [h1]
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => (Finset.univ : Finset L))
      (fun i l => w l * Real.exp (lam * (f i l - μ i)))]
    calc ∏ i, ∑ l, w l * Real.exp (lam * (f i l - μ i))
        ≤ ∏ i : Fin m, Real.exp (lam ^ 2) := by
          apply Finset.prod_le_prod
          · intro i _
            exact Finset.sum_nonneg (fun l _ => mul_nonneg (hw0 l) (Real.exp_pos _).le)
          · intro i _
            apply mgf_step w hw0 hw1 (fun l => f i l - μ i) (hf i)
            · simp only [mul_sub, Finset.sum_sub_distrib, hμ]
              rw [← Finset.sum_mul, hw1]; ring
            · exact hlam
      _ = Real.exp (m * lam ^ 2) := by
          rw [Finset.prod_const, ← Real.exp_nat_mul]; simp
  have hprod_nn : ∀ ω : Fin m → L, 0 ≤ ∏ i, w (ω i) :=
    fun ω => Finset.prod_nonneg (fun i _ => hw0 _)
  calc ∑ ω ∈ Finset.univ.filter (fun ω : Fin m → L =>
        τ ≤ lam * (∑ i, f i (ω i) - ∑ i, ∑ l', w l' * f i l')), ∏ i, w (ω i)
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin m → L =>
        τ ≤ lam * (∑ i, f i (ω i) - ∑ i, ∑ l', w l' * f i l')),
          Real.exp (-τ) * ((∏ i, w (ω i)) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i))) := by
        apply Finset.sum_le_sum
        intro ω hω
        have hω' := (Finset.mem_filter.mp hω).2
        have : Real.exp τ ≤ Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i)) := Real.exp_le_exp.mpr hω'
        have h2 : Real.exp (-τ) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i)) ≥ 1 := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          have := Real.exp_le_exp.mp this
          linarith
        calc ∏ i, w (ω i) = (∏ i, w (ω i)) * 1 := by ring
          _ ≤ (∏ i, w (ω i)) * (Real.exp (-τ) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i))) :=
              mul_le_mul_of_nonneg_left h2 (hprod_nn ω)
          _ = _ := by ring
    _ ≤ ∑ ω : Fin m → L, Real.exp (-τ) * ((∏ i, w (ω i)) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro ω _ _
        exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hprod_nn ω) (Real.exp_pos _).le)
    _ = Real.exp (-τ) * ∑ ω : Fin m → L, (∏ i, w (ω i)) * Real.exp (lam * (∑ i, f i (ω i) - ∑ i, μ i)) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-τ) * Real.exp (m * lam ^ 2) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-τ + m * lam ^ 2) := by rw [← Real.exp_add]

lemma label_f_bound {L : Type} [Fintype L] [DecidableEq L] (w : L → ℝ) (hw0 : ∀ l, 0 ≤ w l)
    (hw1 : ∑ l, w l = 1) (l0 : L) (gi : ℝ) (hg : |gi| ≤ 1) (l : L) :
    |(if l = l0 then gi else 0) - ∑ l', w l' * (if l' = l0 then gi else 0)| ≤ 1 := by
  have hwl : w l0 ≤ 1 := by
    rw [← hw1]
    exact Finset.single_le_sum (fun l _ => hw0 l) (Finset.mem_univ l0)
  have h1 : ∑ l', w l' * (if l' = l0 then gi else 0) = w l0 * gi := by
    simp [Finset.sum_ite_eq']
  rw [h1]
  have := hw0 l0
  split_ifs
  · have e : gi - w l0 * gi = (1 - w l0) * gi := by ring
    rw [e, abs_mul, abs_of_nonneg (by linarith)]
    nlinarith [abs_nonneg gi]
  · rw [zero_sub, abs_neg, abs_mul, abs_of_nonneg (hw0 l0)]
    nlinarith [abs_nonneg gi]

lemma chernoff_label {L : Type} [Fintype L] [DecidableEq L] {m : ℕ} (hm : 0 < m) (w : L → ℝ)
    (hw0 : ∀ l, 0 ≤ w l) (hw1 : ∑ l, w l = 1) (l0 : L) (g : Fin m → ℝ) (hg : ∀ i, |g i| ≤ 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 2 * m) :
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin m → L =>
        w l0 * ∑ i, g i + t ≤ ∑ i, (if ω i = l0 then g i else 0)), ∏ i, w (ω i)
      ≤ Real.exp (-(t ^ 2 / (4 * m)))) ∧
    (∑ ω ∈ Finset.univ.filter (fun ω : Fin m → L =>
        ∑ i, (if ω i = l0 then g i else 0) ≤ w l0 * ∑ i, g i - t), ∏ i, w (ω i)
      ≤ Real.exp (-(t ^ 2 / (4 * m)))) := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  set f : Fin m → L → ℝ := fun i l => if l = l0 then g i else 0 with hf
  have hfb : ∀ i l, |f i l - ∑ l', w l' * f i l'| ≤ 1 := fun i l => label_f_bound w hw0 hw1 l0 (g i) (hg i) l
  have hM : ∑ i, ∑ l', w l' * f i l' = w l0 * ∑ i, g i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [hf, Finset.sum_ite_eq']
  have hexp1 : -(t / (2 * m) * t) + m * (t / (2 * m)) ^ 2 = -(t ^ 2 / (4 * m)) := by
    field_simp; ring
  constructor
  · have hlam : |t / (2 * m)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]; linarith
    have := chernoff_gen w hw0 hw1 f hfb (t / (2 * m)) hlam (t / (2 * m) * t)
    rw [hM, hexp1] at this
    refine le_trans ?_ this
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      have : t ≤ ∑ i, f i (ω i) - w l0 * ∑ i, g i := by simp only [hf]; linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    · intro ω _ _
      exact Finset.prod_nonneg (fun i _ => hw0 _)
  · have hlam : |-(t / (2 * m))| ≤ 1 := by
      rw [abs_neg, abs_of_nonneg (by positivity), div_le_one (by positivity)]; linarith
    have := chernoff_gen w hw0 hw1 f hfb (-(t / (2 * m))) hlam (t / (2 * m) * t)
    rw [hM] at this
    have hexp2 : -(t / (2 * m) * t) + m * (-(t / (2 * m))) ^ 2 = -(t ^ 2 / (4 * m)) := by
      field_simp; ring
    rw [hexp2] at this
    refine le_trans ?_ this
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      have : ∑ i, f i (ω i) - w l0 * ∑ i, g i ≤ -t := by simp only [hf]; linarith
      nlinarith [div_nonneg ht0 (by positivity : (0:ℝ) ≤ 2 * m)]
    · intro ω _ _
      exact Finset.prod_nonneg (fun i _ => hw0 _)



noncomputable def fpm (m k j : ℕ) : ℝ := (m.choose j : ℝ) * (k : ℝ) ^ j * ((m - k : ℕ) : ℝ) ^ (m - j)

lemma fpm_step (m k j : ℕ) (hj : j < m) :
    ((j : ℝ) + 1) * ((m - k : ℕ) : ℝ) * fpm m k (j + 1) = ((m : ℝ) - j) * k * fpm m k j := by
  unfold fpm
  have h1 : (m.choose (j + 1) : ℝ) * ((j : ℝ) + 1) = (m.choose j : ℝ) * ((m : ℝ) - j) := by
    have := Nat.choose_succ_right_eq m j
    have h2 : ((m.choose (j + 1) * (j + 1) : ℕ) : ℝ) = ((m.choose j * (m - j) : ℕ) : ℝ) := by
      rw [this]
    push_cast [Nat.cast_sub hj.le] at h2
    exact h2
  have h3 : m - j = (m - (j + 1)) + 1 := by omega
  have h4 : ((m - k : ℕ) : ℝ) ^ (m - j) = ((m - k : ℕ) : ℝ) ^ (m - (j + 1)) * ((m - k : ℕ) : ℝ) := by
    rw [h3, pow_succ]
  rw [h4]
  calc ((j : ℝ) + 1) * ((m - k : ℕ) : ℝ) * ((m.choose (j + 1) : ℝ) * (k : ℝ) ^ (j + 1) * ((m - k : ℕ) : ℝ) ^ (m - (j + 1)))
      = ((m.choose (j + 1) : ℝ) * ((j : ℝ) + 1)) * (k : ℝ) ^ j * k * (((m - k : ℕ) : ℝ) ^ (m - (j + 1)) * ((m - k : ℕ) : ℝ)) := by ring
    _ = _ := by rw [h1]; ring

lemma fpm_le (m k : ℕ) (hk : k < m) (j : ℕ) (hj : j ≤ m) : fpm m k j ≤ fpm m k k := by
  have hmk : (0:ℝ) < ((m - k : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hk
  have hnn : ∀ j, 0 ≤ fpm m k j := fun j => by unfold fpm; positivity
  rcases le_total j k with h | h
  · -- j ≤ k : increasing up to k
    have key : ∀ d, d ≤ k → fpm m k (k - d) ≤ fpm m k k := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih =>
        intro hd
        have hlt : k - (d + 1) < m := by omega
        have step := fpm_step m k (k - (d + 1)) hlt
        have e : k - (d + 1) + 1 = k - d := by omega
        rw [e] at step
        have h1 := ih (by omega)
        have hpos : 0 < ((k - (d + 1) : ℕ) + 1 : ℝ) * ((m - k : ℕ) : ℝ) := by positivity
        have hineq : (((k - (d + 1) : ℕ) : ℝ) + 1) * ((m - k : ℕ) : ℝ) ≤ ((m : ℝ) - ((k - (d + 1) : ℕ) : ℝ)) * k := by
          have hc : (((k - (d + 1) : ℕ) : ℝ)) + 1 ≤ k := by
            have : k - (d + 1) + 1 ≤ k := by omega
            exact_mod_cast this
          have hmk' : ((m - k : ℕ) : ℝ) = (m:ℝ) - k := by rw [Nat.cast_sub hk.le]
          rw [hmk']
          have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
          nlinarith [hc, hk0, (by exact_mod_cast hk : (k:ℝ) < m)]
        have hfn := hnn (k - (d + 1))
        have : fpm m k (k - (d + 1)) ≤ fpm m k (k - d) := by
          have : (((k - (d + 1) : ℕ) : ℝ) + 1) * ((m - k : ℕ) : ℝ) * fpm m k (k - (d + 1))
              ≤ (((k - (d + 1) : ℕ) : ℝ) + 1) * ((m - k : ℕ) : ℝ) * fpm m k (k - d) := by
            rw [step]
            exact mul_le_mul_of_nonneg_right hineq hfn
          exact le_of_mul_le_mul_left this hpos
        exact this.trans h1
    have := key (k - j) (by omega)
    have e : k - (k - j) = j := by omega
    rwa [e] at this
  · -- k ≤ j : decreasing after k
    induction j, h using Nat.le_induction with
    | base => exact le_rfl
    | succ j hkj ih =>
      have hjm : j < m := by omega
      have step := fpm_step m k j hjm
      have hpos : 0 < ((j : ℝ) + 1) * ((m - k : ℕ) : ℝ) := by positivity
      have hineq : ((m : ℝ) - j) * k ≤ ((j : ℝ) + 1) * ((m - k : ℕ) : ℝ) := by
        have hmk' : ((m - k : ℕ) : ℝ) = (m:ℝ) - k := by rw [Nat.cast_sub hk.le]
        rw [hmk']
        have hkj' : (k:ℝ) ≤ j := by exact_mod_cast hkj
        have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
        nlinarith [hkj', hk0]
      have : fpm m k (j + 1) ≤ fpm m k j := by
        have : ((j : ℝ) + 1) * ((m - k : ℕ) : ℝ) * fpm m k (j + 1)
            ≤ ((j : ℝ) + 1) * ((m - k : ℕ) : ℝ) * fpm m k j := by
          rw [step]
          exact mul_le_mul_of_nonneg_right hineq (hnn j)
        exact le_of_mul_le_mul_left this hpos
      exact this.trans (ih (by omega))

lemma pmf_lower (m k : ℕ) (hk : k < m) :
    (1:ℝ) / (m + 1) ≤ (m.choose k : ℝ) * ((k:ℝ) / m) ^ k * (1 - (k:ℝ) / m) ^ (m - k) := by
  have hm : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsum : ∑ j ∈ Finset.range (m + 1), fpm m k j = (m : ℝ) ^ m := by
    have := add_pow (k : ℝ) (((m - k : ℕ) : ℝ)) m
    have e : (k : ℝ) + ((m - k : ℕ) : ℝ) = m := by
      rw [Nat.cast_sub hk.le]; ring
    rw [e] at this
    rw [this]
    apply Finset.sum_congr rfl
    intro j _
    unfold fpm
    ring
  have hle : ∑ j ∈ Finset.range (m + 1), fpm m k j ≤ (m + 1 : ℕ) * fpm m k k := by
    calc ∑ j ∈ Finset.range (m + 1), fpm m k j ≤ ∑ j ∈ Finset.range (m + 1), fpm m k k :=
          Finset.sum_le_sum (fun j hj => fpm_le m k hk j (by simpa [Nat.lt_succ_iff] using hj))
      _ = _ := by simp
  rw [hsum] at hle
  have hmpos : (0:ℝ) < (m:ℝ) ^ m := by positivity
  have hf : (m.choose k : ℝ) * ((k:ℝ) / m) ^ k * (1 - (k:ℝ) / m) ^ (m - k) = fpm m k k / (m:ℝ) ^ m := by
    unfold fpm
    have e1 : (1 - (k:ℝ) / m) = ((m - k : ℕ) : ℝ) / m := by
      rw [Nat.cast_sub hk.le]; field_simp
    rw [e1, div_pow, div_pow]
    have : (m:ℝ) ^ m = (m:ℝ) ^ k * (m:ℝ) ^ (m - k) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    field_simp
  rw [hf, div_le_div_iff₀ (by positivity) hmpos]
  push_cast at hle
  linarith



/-- label weights -/
noncomputable def wlab (p : ℝ) : Fin 3 → ℝ := ![1 - p, p / 2, p / 2]

lemma wlab_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : ∀ l, 0 ≤ wlab p l := by
  intro l
  fin_cases l <;> simp [wlab] <;> linarith

lemma wlab_sum (p : ℝ) : ∑ l, wlab p l = 1 := by
  simp [wlab, Fin.sum_univ_three]; ring

/-- the labeling attached to a test -/
def omegaOf {m k : ℕ} (t : Test m k) : Fin m → Fin 3 :=
  fun i => if i ∈ t.1.2 then 2 else if i ∈ t.1.1 then 1 else 0

lemma omegaOf_eq_two {m k : ℕ} (t : Test m k) (i : Fin m) : omegaOf t i = 2 ↔ i ∈ t.1.2 := by
  unfold omegaOf
  by_cases a : i ∈ t.1.2 <;> by_cases b : i ∈ t.1.1 <;> simp [a, b]

lemma omegaOf_eq_zero {m k : ℕ} (t : Test m k) (i : Fin m) : omegaOf t i = 0 ↔ i ∉ t.1.1 := by
  unfold omegaOf
  have hs := t.2.2
  by_cases a : i ∈ t.1.2
  · have : i ∈ t.1.1 := hs a
    simp [a, this]
  · by_cases b : i ∈ t.1.1 <;> simp [a, b]

lemma omegaOf_injective {m k : ℕ} : Function.Injective (omegaOf (m := m) (k := k)) := by
  intro t t' h
  apply Subtype.ext
  apply Prod.ext
  · ext i
    have e1 := omegaOf_eq_zero t i
    have e2 := omegaOf_eq_zero t' i
    have h0 := congrFun h i
    rw [h0] at e1
    tauto
  · ext i
    have e1 := omegaOf_eq_two t i
    have e2 := omegaOf_eq_two t' i
    have h0 := congrFun h i
    rw [h0] at e1
    tauto

lemma prod_wlab {m k : ℕ} (p : ℝ) (t : Test m k) :
    ∏ i, wlab p (omegaOf t i) = (1 - p) ^ (m - k) * (p / 2) ^ k := by
  have h1 : ∀ i, wlab p (omegaOf t i) = if i ∈ t.1.1 then p / 2 else 1 - p := by
    intro i
    unfold omegaOf
    have hs := t.2.2
    by_cases a : i ∈ t.1.2 <;> by_cases b : i ∈ t.1.1
    · simp [a, b, wlab]
    · exact absurd (hs a) b
    · simp [a, b, wlab]
    · simp [a, b, wlab]
  simp_rw [h1]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hc : t.1.1.card = k := t.2.1
  have : (Finset.univ.filter (fun i => i ∉ t.1.1)).card = m - k := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
    simp [hc]
  have h2 : (Finset.univ.filter (fun i => i ∈ t.1.1)).card = k := by simpa using hc
  rw [h2, this]; ring

lemma ratio_alg (H0 n H1 N' r ε k : ℝ) (hn : 0 < n) (hN : 0 < N') (hε : 0 < ε)
    (h1 : H0 - r * n < ε * n / 2) (h2 : -(ε * k / 8) < H1 - r * N') (h3 : k / 4 < N') :
    H0 / n ≤ H1 / N' + ε := by
  have a1 : H0 / n < r + ε / 2 := by
    rw [div_lt_iff₀ hn]; nlinarith
  have a2 : r - ε / 2 ≤ H1 / N' := by
    rw [le_div_iff₀ hN]; nlinarith
  linarith

lemma sum_ite_omega {m k : ℕ} (t : Test m k) (g : Fin m → ℝ) :
    ∑ i, (if omegaOf t i = 0 then g i else 0) = ∑ i ∈ t.1.1ᶜ, g i := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp [omegaOf_eq_zero]

lemma sum_ite_omega2 {m k : ℕ} (t : Test m k) (g : Fin m → ℝ) :
    ∑ i, (if omegaOf t i = 2 then g i else 0) = ∑ i ∈ t.1.2, g i := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp [omegaOf_eq_two]

noncomputable def indd {m : ℕ} (x xhat : Fin m → Bool) (i : Fin m) : ℝ := if x i ≠ xhat i then 1 else 0

lemma hamming_real {m : ℕ} (S : Finset (Fin m)) (x xhat : Fin m → Bool) :
    (hammingOn S x xhat : ℝ) = ∑ i ∈ S, indd x xhat i := by
  unfold hammingOn indd
  rw [Finset.card_filter]
  push_cast
  rfl

lemma bad_to_events {m k : ℕ} (hk1 : 1 ≤ k) (hkm : k < m) (ε : ℝ) (hε : 0 < ε)
    (x xhat : Fin m → Bool) (t : Test m k) (ht : x ∉ goodSet ε xhat t) :
    (wlab ((k:ℝ) / m) 0 * ∑ i, (indd x xhat i - (∑ j, indd x xhat j) / m) + ε * ((m:ℝ) - k) / 2 ≤
        ∑ i, (if omegaOf t i = 0 then (indd x xhat i - (∑ j, indd x xhat j) / m) else 0)) ∨
    (∑ i, (if omegaOf t i = 2 then (indd x xhat i - (∑ j, indd x xhat j) / m) else 0) ≤
        wlab ((k:ℝ) / m) 2 * ∑ i, (indd x xhat i - (∑ j, indd x xhat j) / m) - ε * k / 8) ∨
    (∑ i, (if omegaOf t i = 2 then (1:ℝ) else 0) ≤
        wlab ((k:ℝ) / m) 2 * ∑ i : Fin m, (1:ℝ) - (k:ℝ) / 4) := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨hA, hB, hC⟩ := hcon
  have hm : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hsg : ∑ i, (indd x xhat i - (∑ j, indd x xhat j) / m) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  rw [hsg, sum_ite_omega, mul_zero, zero_add] at hA
  rw [hsg, sum_ite_omega2, mul_zero, zero_sub] at hB
  rw [sum_ite_omega2] at hC
  have hw2 : wlab ((k:ℝ) / m) 2 = (k:ℝ) / m / 2 := by simp [wlab]
  rw [hw2] at hC
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hC
  have hcT : t.1.1.card = k := t.2.1
  have hcn : (t.1.1ᶜ.card : ℝ) = (m:ℝ) - k := by
    rw [Finset.card_compl, hcT, Fintype.card_fin, Nat.cast_sub hkm.le]
  have hsum1 : ∑ i ∈ t.1.1ᶜ, (indd x xhat i - (∑ j, indd x xhat j) / m)
      = (hammingOn t.1.1ᶜ x xhat : ℝ) - (∑ j, indd x xhat j) / m * (t.1.1ᶜ.card : ℝ) := by
    rw [Finset.sum_sub_distrib, hamming_real]
    simp
    ring
  have hsum2 : ∑ i ∈ t.1.2, (indd x xhat i - (∑ j, indd x xhat j) / m)
      = (hammingOn t.1.2 x xhat : ℝ) - (∑ j, indd x xhat j) / m * (t.1.2.card : ℝ) := by
    rw [Finset.sum_sub_distrib, hamming_real]
    simp
    ring
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk1
  have hN : (k:ℝ) / 4 < (t.1.2.card : ℝ) := by
    have : (k:ℝ) / m / 2 * m = k / 2 := by field_simp
    rw [this] at hC
    linarith
  have hkmR : (k:ℝ) < m := by exact_mod_cast hkm
  have hn : (0:ℝ) < (t.1.1ᶜ.card : ℝ) := by rw [hcn]; linarith
  have key := ratio_alg (hammingOn t.1.1ᶜ x xhat) (t.1.1ᶜ.card) (hammingOn t.1.2 x xhat) (t.1.2.card)
    ((∑ j, indd x xhat j) / m) ε k hn (by linarith) hε
    (by rw [hsum1, hcn] at hA; rw [hcn]; linarith)
    (by rw [hsum2] at hB; linarith) hN
  apply ht
  simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold relHamming
  exact key



lemma gen_exp (θ T c m : ℝ) (hm : 0 < m) (hθ : 0 ≤ θ) (hT : θ * m ≤ T) (hc : c ≤ θ ^ 2 / 4) :
    c * m ≤ T ^ 2 / (4 * m) := by
  rw [le_div_iff₀ (by positivity)]
  have h1 : (θ * m) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by positivity) hT 2
  nlinarith [mul_pos hm hm]

lemma sum_filter_or_le {α : Type} [Fintype α] (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (P Q R : α → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R] [DecidablePred (fun a => P a ∨ Q a ∨ R a)] :
    ∑ a ∈ Finset.univ.filter (fun a => P a ∨ Q a ∨ R a), f a ≤
      ∑ a ∈ Finset.univ.filter P, f a + ∑ a ∈ Finset.univ.filter Q, f a
        + ∑ a ∈ Finset.univ.filter R, f a := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have := hf a
  by_cases hP : P a <;> by_cases hQ : Q a <;> by_cases hR : R a <;> simp [hP, hQ, hR, this]

theorem samp_main (α ε : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) (hm : 2 / α ≤ m) (x xhat : Fin m → Bool) :
    ∑ t ∈ Finset.univ.filter (fun t : Test m ⌊α * m⌋₊ => x ∉ goodSet ε xhat t),
        testProb m ⌊α * m⌋₊ t ≤
      (m + 1) * (3 * Real.exp (-((ε * min (1 - α) α) ^ 2 / 1024 * m))) := by
  classical
  have hmpos : (0:ℝ) < m := lt_of_lt_of_le (by positivity) hm
  have hm0 : 0 < m := by exact_mod_cast hmpos
  have hαm : 2 ≤ α * m := by
    have := (div_le_iff₀ hα0).mp hm
    linarith
  set k : ℕ := ⌊α * m⌋₊ with hk
  have hkle : (k:ℝ) ≤ α * m := Nat.floor_le (by positivity)
  have hklt : α * m < k + 1 := Nat.lt_floor_add_one _
  have hkge : α * m / 2 ≤ k := by linarith
  have hk1R : (1:ℝ) ≤ k := by linarith
  have hk1 : 1 ≤ k := by exact_mod_cast hk1R
  have hkmR : (k:ℝ) < m := by nlinarith
  have hkm : k < m := by exact_mod_cast hkmR
  set p : ℝ := (k:ℝ) / m with hp
  have hp0 : 0 < p := div_pos (by linarith) hmpos
  have hp1 : p < 1 := (div_lt_one hmpos).mpr hkmR
  set g : Fin m → ℝ := fun i => indd x xhat i - (∑ j, indd x xhat j) / m with hg
  have hind01 : ∀ i, 0 ≤ indd x xhat i ∧ indd x xhat i ≤ 1 := by
    intro i; unfold indd; split_ifs <;> simp
  have hr01 : 0 ≤ (∑ j, indd x xhat j) / m ∧ (∑ j, indd x xhat j) / m ≤ 1 := by
    constructor
    · exact div_nonneg (Finset.sum_nonneg (fun i _ => (hind01 i).1)) hmpos.le
    · rw [div_le_one hmpos]
      calc ∑ j, indd x xhat j ≤ ∑ j : Fin m, (1:ℝ) := Finset.sum_le_sum (fun i _ => (hind01 i).2)
        _ = m := by simp
  have hgb : ∀ i, |g i| ≤ 1 := by
    intro i
    simp only [hg]
    rw [abs_le]
    constructor <;> linarith [(hind01 i).1, (hind01 i).2, hr01.1, hr01.2]
  have hw0 := wlab_nonneg hp0.le hp1.le
  have hw1 := wlab_sum p
  set tA : ℝ := ε * ((m:ℝ) - k) / 2 with htA
  set tB : ℝ := ε * k / 8 with htB
  set tC : ℝ := (k:ℝ) / 4 with htC
  have hA := (chernoff_label hm0 (wlab p) hw0 hw1 0 g hgb tA (by rw [htA]; nlinarith)
    (by rw [htA]; nlinarith)).1
  have hB := (chernoff_label hm0 (wlab p) hw0 hw1 2 g hgb tB (by rw [htB]; positivity)
    (by rw [htB]; nlinarith)).2
  have hC := (chernoff_label hm0 (wlab p) hw0 hw1 2 (fun _ => (1:ℝ)) (fun _ => by simp) tC
    (by rw [htC]; positivity) (by rw [htC]; nlinarith)).2
  set c₀ : ℝ := (ε * min (1 - α) α) ^ 2 / 1024 with hc₀
  have hδ1 : min (1 - α) α ≤ 1 - α := min_le_left _ _
  have hδ2 : min (1 - α) α ≤ α := min_le_right _ _
  have hδ0 : 0 ≤ min (1 - α) α := le_min (by linarith) hα0.le
  set δ : ℝ := min (1 - α) α with hδ
  have hδm1 : δ * m ≤ (m:ℝ) - k := by
    have := mul_le_mul_of_nonneg_right hδ1 hmpos.le
    linarith
  have hδm2 : δ * m / 2 ≤ k := by
    have := mul_le_mul_of_nonneg_right hδ2 hmpos.le
    linarith
  have hεδ : (0:ℝ) ≤ (ε * δ) ^ 2 := sq_nonneg _
  have hexpA : c₀ * m ≤ tA ^ 2 / (4 * m) := by
    apply gen_exp (ε * δ / 2) _ _ _ hmpos (by positivity)
    · rw [htA]
      have := mul_le_mul_of_nonneg_left hδm1 hε0.le
      linarith
    · rw [hc₀]
      linarith
  have hexpB : c₀ * m ≤ tB ^ 2 / (4 * m) := by
    apply gen_exp (ε * δ / 16) _ _ _ hmpos (by positivity)
    · rw [htB]
      have := mul_le_mul_of_nonneg_left hδm2 hε0.le
      linarith
    · rw [hc₀]
      have : (ε * δ / 16) ^ 2 / 4 = (ε * δ) ^ 2 / 1024 := by ring
      linarith
  have hexpC : c₀ * m ≤ tC ^ 2 / (4 * m) := by
    apply gen_exp (δ / 8) _ _ _ hmpos (by positivity)
    · rw [htC]
      linarith
    · rw [hc₀]
      have h6 : (ε * δ) ^ 2 ≤ δ ^ 2 := by
        rw [mul_pow]
        exact mul_le_of_le_one_left (sq_nonneg δ) (pow_le_one₀ hε0.le hε1)
      have : (δ / 8) ^ 2 / 4 = δ ^ 2 / 256 := by ring
      linarith
  have hSA := hA.trans (Real.exp_le_exp.mpr (neg_le_neg hexpA))
  have hSB := hB.trans (Real.exp_le_exp.mpr (neg_le_neg hexpB))
  have hSC := hC.trans (Real.exp_le_exp.mpr (neg_le_neg hexpC))
  set wtf : (Fin m → Fin 3) → ℝ := fun ω => ∏ i, wlab p (ω i) with hwtf
  have hwnn : ∀ ω, 0 ≤ wtf ω := fun ω => Finset.prod_nonneg (fun i _ => hw0 _)
  set bad := Finset.univ.filter (fun t : Test m k => x ∉ goodSet ε xhat t) with hbad
  have h1p : 0 < 1 - p := by linarith
  set q : ℝ := (1 - p) ^ (m - k) * (p / 2) ^ k with hq
  have hqpos : 0 < q := by positivity
  have hmain : q * bad.card ≤ 3 * Real.exp (-(c₀ * m)) := by
    calc q * bad.card = ∑ t ∈ bad, wtf (omegaOf t) := by
          rw [Finset.sum_congr rfl (fun t _ => prod_wlab p t)]
          simp [hq, mul_comm]
      _ = ∑ ω ∈ bad.image omegaOf, wtf ω :=
          (Finset.sum_image (fun a _ b _ h => omegaOf_injective h)).symm
      _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin m → Fin 3 =>
            (wlab p 0 * ∑ i, g i + tA ≤ ∑ i, (if ω i = 0 then g i else 0)) ∨
            (∑ i, (if ω i = 2 then g i else 0) ≤ wlab p 2 * ∑ i, g i - tB) ∨
            (∑ i, (if ω i = 2 then (1:ℝ) else 0) ≤ wlab p 2 * ∑ i : Fin m, (1:ℝ) - tC)), wtf ω := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro ω hω
            obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hω
            have ht' : x ∉ goodSet ε xhat t := (Finset.mem_filter.mp ht).2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact bad_to_events hk1 hkm ε hε0 x xhat t ht'
          · intro ω _ _
            exact hwnn ω
      _ ≤ _ := sum_filter_or_le wtf hwnn _ _ _
      _ ≤ 3 * Real.exp (-(c₀ * m)) := by linarith
  have hL : 1 / ((m:ℝ) + 1) ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := pmf_lower m k hkm
  have hCpos : (0:ℝ) < (m.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkm.le
  set Z : ℝ := (m.choose k : ℝ) * 2 ^ k with hZ
  have hZpos : 0 < Z := by positivity
  have hqZ : q * Z = (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by
    rw [hq, hZ, div_pow]
    field_simp
  have hE0 : 0 ≤ 3 * Real.exp (-(c₀ * m)) := by positivity
  have hsum : ∑ t ∈ bad, testProb m k t = bad.card * Z⁻¹ := by
    calc ∑ t ∈ bad, testProb m k t = ∑ t ∈ bad, Z⁻¹ := Finset.sum_congr rfl (fun t _ => rfl)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [hsum, ← div_eq_mul_inv, div_le_iff₀ hZpos]
  have hmp1 : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have hone : (1:ℝ) ≤ ((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) * ((m:ℝ) + 1) :=
    (div_le_iff₀ hmp1).mp hL
  have hkey : q * bad.card ≤ q * (((m:ℝ) + 1) * (3 * Real.exp (-(c₀ * m))) * Z) := by
    calc q * bad.card ≤ 3 * Real.exp (-(c₀ * m)) := hmain
      _ = (3 * Real.exp (-(c₀ * m))) * 1 := by ring
      _ ≤ (3 * Real.exp (-(c₀ * m))) * (((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) * ((m:ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hone hE0
      _ = q * (((m:ℝ) + 1) * (3 * Real.exp (-(c₀ * m))) * Z) := by rw [← hqZ]; ring
  exact le_of_mul_le_mul_left hkey hqpos


lemma exp_decay_negl (c₀ : ℝ) (hc₀ : 0 < c₀) (c : ℕ) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → 3 * ((m:ℝ) + 1) * Real.exp (-(c₀ * m)) ≤ ((m:ℝ) ^ c)⁻¹ ∧ 1 ≤ m := by
  have h1 : Filter.Tendsto (fun x : ℝ => x ^ (c + 1) * Real.exp (-x)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (c + 1)
  have h2 : Filter.Tendsto (fun m : ℕ => c₀ * (m:ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc₀ tendsto_natCast_atTop_atTop
  have h3 := h1.comp h2
  have h4 : Filter.Tendsto (fun m : ℕ => (m:ℝ) ^ (c + 1) * Real.exp (-(c₀ * m))) Filter.atTop (nhds 0) := by
    have := h3.div_const (c₀ ^ (c + 1))
    simp only [zero_div] at this
    refine this.congr (fun m => ?_)
    simp only [Function.comp]
    rw [mul_pow]
    field_simp
  have h5 := h4.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1 / 6))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h5
  refine ⟨max N 1, fun m hm => ?_⟩
  have hmN : N ≤ m := le_trans (le_max_left _ _) hm
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  refine ⟨?_, hm1⟩
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hmpos : (0:ℝ) < m := by linarith
  have := hN m hmN
  rw [← one_div, le_div_iff₀ (pow_pos hmpos c)]
  have hexp := (Real.exp_pos (-(c₀ * m))).le
  calc 3 * ((m:ℝ) + 1) * Real.exp (-(c₀ * m)) * (m:ℝ) ^ c
      ≤ 3 * (2 * (m:ℝ)) * Real.exp (-(c₀ * m)) * (m:ℝ) ^ c := by
        have : (m:ℝ) + 1 ≤ 2 * m := by linarith
        have h0 : 0 ≤ Real.exp (-(c₀ * m)) * (m:ℝ) ^ c := mul_nonneg hexp (pow_pos hmpos c).le
        nlinarith
    _ = 6 * ((m:ℝ) ^ (c + 1) * Real.exp (-(c₀ * m))) := by ring
    _ ≤ 1 := by linarith


theorem sampling_aux (α ε : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ (m : ℕ) (x xhat : Fin m → Bool),
        ∑ t ∈ Finset.univ.filter (fun t : Test m ⌊α * m⌋₊ => x ∉ goodSet ε xhat t),
          testProb m ⌊α * m⌋₊ t ≤ ν m := by
  classical
  set ε₁ : ℝ := min ε 1 with hε₁
  have hε10 : 0 < ε₁ := lt_min hε one_pos
  have hε11 : ε₁ ≤ 1 := min_le_right _ _
  have hε1ε : ε₁ ≤ ε := min_le_left _ _
  set δ : ℝ := min (1 - α) α with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) hα0
  set c₀ : ℝ := (ε₁ * δ) ^ 2 / 1024 with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  let ν : ℕ → ℝ := fun m =>
    if 2 / α ≤ (m:ℝ) then ((m:ℝ) + 1) * (3 * Real.exp (-(c₀ * m)))
    else ∑ t : Test m ⌊α * m⌋₊, testProb m ⌊α * m⌋₊ t
  refine ⟨ν, ?_, ?_⟩
  · intro c
    obtain ⟨N, hN⟩ := exp_decay_negl c₀ hc₀pos c
    refine ⟨max N ⌈2 / α⌉₊, fun m hm => ?_⟩
    have hmN : N ≤ m := le_trans (le_max_left _ _) hm
    have hm2 : 2 / α ≤ (m:ℝ) := by
      have : ⌈2 / α⌉₊ ≤ m := le_trans (le_max_right _ _) hm
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
    obtain ⟨h1, h2⟩ := hN m hmN
    simp only [ν, if_pos hm2]
    rw [abs_of_nonneg (by positivity)]
    calc ((m:ℝ) + 1) * (3 * Real.exp (-(c₀ * m))) = 3 * ((m:ℝ) + 1) * Real.exp (-(c₀ * m)) := by ring
      _ ≤ _ := h1
  · intro m x xhat
    by_cases hm : 2 / α ≤ (m:ℝ)
    · simp only [ν, if_pos hm]
      calc ∑ t ∈ Finset.univ.filter (fun t : Test m ⌊α * m⌋₊ => x ∉ goodSet ε xhat t),
            testProb m ⌊α * m⌋₊ t
          ≤ ∑ t ∈ Finset.univ.filter (fun t : Test m ⌊α * m⌋₊ => x ∉ goodSet ε₁ xhat t),
            testProb m ⌊α * m⌋₊ t := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro t ht
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
              intro hx
              apply ht
              simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              linarith
            · intro t _ _
              unfold testProb; positivity
        _ ≤ _ := samp_main α ε₁ hα0 hα1 hε10 hε11 m hm x xhat
    · simp only [ν, if_neg hm]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro t _ _
      unfold testProb; positivity


theorem lemma43_aux (α ε : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ (m : ℕ) (xhat θhat : Fin m → Bool) (E : Type) [Fintype E] [DecidableEq E]
        (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)), ‖φ‖ = 1 →
        ∃ φt : Test m ⌊α * m⌋₊ → EuclideanSpace ℂ ((Fin m → Bool) × E),
          (∀ t, ‖φt t‖ = 1) ∧
          (∀ t y, y ∉ goodSet ε xhat t → amp θhat y (φt t) = 0) ∧
          traceDistance (cqState (fun _ : Test m ⌊α * m⌋₊ => φ)) (cqState φt) ≤ ν m := by
  obtain ⟨νs, hneg, hbd⟩ := sampling_aux α ε hα0 hα1 hε
  refine ⟨fun m => Real.sqrt (νs m), ?_, ?_⟩
  · intro c
    obtain ⟨N, hN⟩ := hneg (2 * c)
    refine ⟨max N 1, fun m hm => ?_⟩
    have hmN : N ≤ m := le_trans (le_max_left _ _) hm
    have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have := hN m hmN
    calc νs m ≤ |νs m| := le_abs_self _
      _ ≤ ((m:ℝ) ^ (2 * c))⁻¹ := this
      _ = (((m:ℝ) ^ c)⁻¹) ^ 2 := by rw [inv_pow, ← pow_mul, mul_comm c 2]
  · intro m xhat θhat E _ _ φ hφ
    obtain ⟨φt, h1, h2, h3⟩ := lemma43_core (k := ⌊α * m⌋₊) ε hε xhat θhat E φ hφ (νs m)
      (fun y => hbd m y xhat)
    exact ⟨φt, h1, h2, h3⟩

lemma exists_small_eps (β : ℝ) (hβ : 0 < β) : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧ binEntropy2 ε ≤ β := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcont : ContinuousAt Real.binEntropy 0 := Real.binEntropy_continuous.continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hδ'⟩ := hcont (β * Real.log 2) (by positivity)
  refine ⟨min (δ / 2) (1 / 2), lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  have hpos : 0 < min (δ / 2) (1 / 2) := lt_min (by positivity) (by norm_num)
  have hd : dist (min (δ / 2) (1 / 2)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have := hδ' hd
  rw [Real.dist_eq, Real.binEntropy_zero, sub_zero] at this
  have h2 := (abs_lt.mp this).2
  unfold binEntropy2
  rw [div_le_iff₀ hlog]
  linarith

theorem forces_aux (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ (m : ℕ) (xhat θhat : Fin m → Bool) (E : Type) [Fintype E] [DecidableEq E]
        (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)), ‖φ‖ = 1 →
        ∃ φt : Test m ⌊α * m⌋₊ → EuclideanSpace ℂ ((Fin m → Bool) × E),
          (∀ t, ‖φt t‖ = 1) ∧
          traceDistance (cqState (fun _ : Test m ⌊α * m⌋₊ => φ)) (cqState φt) ≤ ν m ∧
          ∀ (t : Test m ⌊α * m⌋₊) (θ x : Fin m → Bool),
            (∀ i ∈ t.1.2, x i = xhat i) →
            0 < ∑ y ∈ agreeOn t.1.1 x, outcomeProb (mixBasis t.1.1 θhat θ) (φt t) y →
            maxEntropy (bobState (mixBasis t.1.1 θhat θ) (φt t) t.1.1 x) ≤
                β * ((m - ⌊α * m⌋₊ : ℕ) : ℝ) ∧
              ∀ I : Finset (Fin m), I ⊆ t.1.1ᶜ →
                0 < ∑ y ∈ agreeOn Iᶜ x, outcomeProb (mixBasis t.1.1 θhat θ) (φt t) y →
                (hammingOn I θ θhat : ℝ) - β * ((m - ⌊α * m⌋₊ : ℕ) : ℝ) ≤
                  condMinEntropy (outcomeProb (mixBasis t.1.1 θhat θ) (φt t)) I x := by
  obtain ⟨ε, hε0, hε1, hεβ⟩ := exists_small_eps β hβ
  obtain ⟨ν, hneg, hν⟩ := lemma43_aux α ε hα0 hα1 hε0
  refine ⟨ν, hneg, ?_⟩
  intro m xhat θhat E _ _ φ hφ
  obtain ⟨φt, h1, h2, h3⟩ := hν m xhat θhat E φ hφ
  refine ⟨φt, h1, h3, ?_⟩
  intro t θ x hxt hpos
  have hrel : relHamming t.1.2 x xhat = 0 := by
    unfold relHamming hammingOn
    have : t.1.2.filter (fun i => x i ≠ xhat i) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi
      simp [hxt i hi]
    rw [this]; simp
  have herr : relHamming t.1.2 x xhat + ε ≤ 1 / 2 := by rw [hrel]; linarith
  have hcor := cor44_aux ε hε0 xhat θhat θ t (φt t) (h1 t) (h2 t) x herr hpos
  rw [hrel, zero_add] at hcor
  have hcard : ((m - ⌊α * m⌋₊ : ℕ) : ℝ) = (t.1.1ᶜ.card : ℝ) := by
    rw [Finset.card_compl, t.2.1, Fintype.card_fin]
  rw [hcard]
  have hn0 : (0:ℝ) ≤ (t.1.1ᶜ.card : ℝ) := Nat.cast_nonneg _
  have hle : binEntropy2 ε * (t.1.1ᶜ.card : ℝ) ≤ β * (t.1.1ᶜ.card : ℝ) :=
    mul_le_mul_of_nonneg_right hεβ hn0
  refine ⟨hcor.1.trans hle, ?_⟩
  intro I hI hposI
  have := hcor.2 I hI hposI
  linarith

end CommitOpen.Benign

open CommitOpen.Benign

theorem solution (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hβ : 0 < β) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      ∀ (m : ℕ) (xhat θhat : Fin m → Bool) (E : Type) [Fintype E] [DecidableEq E]
        (φ : EuclideanSpace ℂ ((Fin m → Bool) × E)), ‖φ‖ = 1 →
        ∃ φt : Test m ⌊α * m⌋₊ → EuclideanSpace ℂ ((Fin m → Bool) × E),
          (∀ t, ‖φt t‖ = 1) ∧
          traceDistance (cqState (fun _ : Test m ⌊α * m⌋₊ => φ)) (cqState φt) ≤ ν m ∧
          ∀ (t : Test m ⌊α * m⌋₊) (θ x : Fin m → Bool),
            (∀ i ∈ t.1.2, x i = xhat i) →
            0 < ∑ y ∈ agreeOn t.1.1 x, outcomeProb (mixBasis t.1.1 θhat θ) (φt t) y →
            maxEntropy (bobState (mixBasis t.1.1 θhat θ) (φt t) t.1.1 x) ≤
                β * ((m - ⌊α * m⌋₊ : ℕ) : ℝ) ∧
              ∀ I : Finset (Fin m), I ⊆ t.1.1ᶜ →
                0 < ∑ y ∈ agreeOn Iᶜ x, outcomeProb (mixBasis t.1.1 θhat θ) (φt t) y →
                (hammingOn I θ θhat : ℝ) - β * ((m - ⌊α * m⌋₊ : ℕ) : ℝ) ≤
                  condMinEntropy (outcomeProb (mixBasis t.1.1 θhat θ) (φt t)) I x :=
  forces_aux α β hα0 hα1 hβ
