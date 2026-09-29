-- Prove2me | solution 1 for FatkhullinPolyak.Discrete.sublevel_bounded
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:15:17.030112+00:00
-- url     : https://prove2.me/submissions/f987cb44-c0df-4f8f-b9e8-af2f0248ad65

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

open Matrix Polynomial

lemma aux_sb_poly_comm {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℝ)
    (h : M.transpose * X + X * M = 0) (p : ℝ[X]) :
    aeval M.transpose p * X = X * aeval (-M) p := by
  have h' : M.transpose * X = X * (-M) := by
    rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left h
  have hk : ∀ k : ℕ, M.transpose ^ k * X = X * (-M) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, h', Matrix.mul_assoc, ← pow_succ']
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mul, hk, Matrix.mul_smul]

lemma aux_sb_unit {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    IsUnit (aeval (-M) M.charpoly) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact isUnit_of_subsingleton _
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set f : Matrix (Fin n) (Fin n) ℝ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (Algebra.ofId ℝ ℂ).mapMatrix with hf
  have key : IsUnit (f (aeval (-M) M.charpoly)) := by
    rw [← aeval_algHom_apply, ← aeval_map_algebraMap ℂ]
    have hc : M.charpoly.map (algebraMap ℝ ℂ) = (M.map (algebraMap ℝ ℂ)).charpoly :=
      (Matrix.charpoly_map M (algebraMap ℝ ℂ)).symm
    have hfM : f (-M) = -(M.map (algebraMap ℝ ℂ)) := by
      rw [map_neg]; rfl
    rw [hc, hfM, ← spectrum.zero_notMem_iff ℂ,
      spectrum.map_polynomial_aeval_of_degree_pos]
    · rintro ⟨z, hz, hz0⟩
      have h1 : z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) :=
        Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hz0
      rw [← spectrum.neg_eq] at hz
      have h2 : -z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) := by
        simpa using hz
      have := hM z h1
      have := hM (-z) h2
      simp at this
      linarith
    · rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
      exact_mod_cast hn
  rw [Matrix.isUnit_iff_isUnit_det] at key ⊢
  rw [isUnit_iff_ne_zero] at key ⊢
  intro h0
  apply key
  have : (f (aeval (-M) M.charpoly)).det = algebraMap ℝ ℂ (aeval (-M) M.charpoly).det :=
    (RingHom.map_det (algebraMap ℝ ℂ) _).symm
  rw [this, h0, map_zero]

lemma aux_sb_inj {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (h : M.transpose * X + X * M = 0) : X = 0 := by
  have h1 := aux_sb_poly_comm M X h M.charpoly
  have hz : aeval M.transpose M.charpoly = 0 := by
    rw [← Matrix.charpoly_transpose]; exact Matrix.aeval_self_charpoly _
  rw [hz, zero_mul] at h1
  exact ((aux_sb_unit M hM).mul_left_eq_zero).mp h1.symm


/-- The Lyapunov operator `X ↦ Mᵀ X + X M`. -/
noncomputable def aux_sb_L {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun X := M.transpose * X + X * M
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' c X := by simp [smul_add]

lemma aux_sb_L_apply {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℝ) :
    aux_sb_L M X = M.transpose * X + X * M := rfl

lemma aux_sb_L_inj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M) :
    Function.Injective (aux_sb_L M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro X hX
  exact aux_sb_inj M X hM hX

lemma aux_sb_exists_unique {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (W : Matrix (Fin n) (Fin n) ℝ) : ∃! X : Matrix (Fin n) (Fin n) ℝ,
      M.transpose * X + X * M + W = 0 := by
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective.mp (aux_sb_L_inj M hM)) (-W)
  rw [aux_sb_L_apply] at hX
  refine ⟨X, ?_, ?_⟩
  · show M.transpose * X + X * M + W = 0
    rw [hX]; simp
  · intro Y hY
    apply aux_sb_L_inj M hM
    rw [aux_sb_L_apply, aux_sb_L_apply, hX]
    exact eq_neg_of_add_eq_zero_left hY

lemma aux_sb_lyapSol_spec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    M.transpose * lyapSol M W + lyapSol M W * M + W = 0 := by
  have h := aux_sb_exists_unique M hM W
  unfold lyapSol
  rw [dif_pos h]
  exact h.choose_spec.1

lemma aux_sb_symm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsHurwitz M)
    (W X : Matrix (Fin n) (Fin n) ℝ) (hW : W.transpose = W)
    (hX : M.transpose * X + X * M + W = 0) : X.transpose = X := by
  obtain ⟨Y, hY, huniq⟩ := aux_sb_exists_unique M hM W
  have h1 := huniq X hX
  have h2 : M.transpose * X.transpose + X.transpose * M + W = 0 := by
    have := congrArg Matrix.transpose hX
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, hW,
      Matrix.transpose_zero] at this
    rw [← this]; abel
  rw [huniq _ h2, h1]

lemma aux_sb_hom_hurwitz {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsHurwitz A) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsHurwitz ((1 - s) • A - s • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  intro z hz
  by_contra hre
  replace hre := not_lt.mp hre
  rw [spectrum.mem_iff] at hz
  apply hz
  set Ac := A.map (algebraMap ℝ ℂ) with hAc
  have hmap : ((1 - s) • A - s • (1 : Matrix (Fin n) (Fin n) ℝ)).map (algebraMap ℝ ℂ)
      = (1 - (s : ℂ)) • Ac - (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    simp only [hAc, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs <;> simp
  rw [hmap]
  rcases eq_or_lt_of_le hs1 with rfl | hs1'
  · have hz1 : z + 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have : algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) z - ((1 - ((1 : ℝ) : ℂ)) • Ac
        - ((1 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
        = algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (z + 1) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
      simp only [Complex.ofReal_one, sub_self, zero_smul, one_smul, add_smul]
      abel
    rw [this]
    exact (isUnit_iff_ne_zero.mpr hz1).map _
  · have hc : (1 - (s : ℂ)) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    set w := (z + s) / (1 - (s : ℂ)) with hw
    have hwre : 0 ≤ w.re := by
      have h1s : (1 - (s : ℂ)) = ((1 - s : ℝ) : ℂ) := by push_cast; ring
      rw [hw, h1s, Complex.div_ofReal_re]
      apply div_nonneg
      · simp; linarith
      · linarith
    have hwn : w ∉ spectrum ℂ Ac := fun h => by
      have := hA w h
      linarith
    rw [spectrum.notMem_iff] at hwn
    have hw' : (1 - (s : ℂ)) * w = z + s := mul_div_cancel₀ _ hc
    have : algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) z - ((1 - (s : ℂ)) • Ac
        - (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))
        = algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (1 - (s : ℂ)) *
          (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) w - Ac) := by
      rw [← Algebra.smul_def, smul_sub, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, smul_smul, hw', add_smul]
      abel
    rw [this]
    exact ((isUnit_iff_ne_zero.mpr hc).map _).mul hwn


lemma aux_sb_quad_scale {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (v : Fin n → ℝ) :
    (c • v) ⬝ᵥ (Y *ᵥ (c • v)) = c ^ 2 * (v ⬝ᵥ (Y *ᵥ v)) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring

lemma aux_sb_Y_zero {n : ℕ} (M Y W : Matrix (Fin n) (Fin n) ℝ) (hY : Y.transpose = Y)
    (hMY : M.transpose * Y + Y * M + W = 0) (v : Fin n → ℝ) (hv : Y *ᵥ v = 0) :
    v ⬝ᵥ (W *ᵥ v) = 0 := by
  have h := congrArg (fun Z => v ⬝ᵥ (Z *ᵥ v)) hMY
  simp only [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
    dotProduct_zero, zero_add, Matrix.zero_mulVec] at h
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hY, hv, zero_dotProduct,
    zero_add] at h
  exact h

/-- The Lyapunov operator on the plain function space `Fin n → Fin n → ℝ`. -/
noncomputable def aux_sb_LE {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → Fin n → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℝ) where
  toFun X := (M.transpose * Matrix.of X + Matrix.of X * M : Matrix (Fin n) (Fin n) ℝ)
  map_add' X Y := (aux_sb_L M).map_add X Y
  map_smul' c X := (aux_sb_L M).map_smul c X

lemma aux_sb_psd {n : ℕ} (A W X : Matrix (Fin n) (Fin n) ℝ) (hA : IsHurwitz A)
    (hWs : W.transpose = W) (hW : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (W *ᵥ v))
    (hX : A.transpose * X + X * A + W = 0) :
    ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (X *ᵥ v) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v0, hv0⟩ := hcon
  have hv0ne : v0 ≠ 0 := by
    rintro rfl; simp at hv0
  have : Nontrivial (Fin n → ℝ) := nontrivial_of_ne v0 0 hv0ne
  set As : ℝ → Matrix (Fin n) (Fin n) ℝ :=
    fun s => (1 - s) • A - s • (1 : Matrix (Fin n) (Fin n) ℝ) with hAs
  set Lc : ℝ → ((Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ)) :=
    fun s => LinearMap.toContinuousLinearMap (aux_sb_LE (As s)) with hLc
  have hLc_cont : Continuous Lc := by
    refine continuous_clm_apply.mpr fun Y => ?_
    show Continuous fun s => ((As s).transpose * Matrix.of Y + Matrix.of Y * As s :
      Matrix (Fin n) (Fin n) ℝ)
    simp only [hAs]
    fun_prop
  have hunit : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ u : ((Fin n → Fin n → ℝ) →L[ℝ]
      (Fin n → Fin n → ℝ))ˣ, (u : (Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ)) = Lc s := by
    intro s hs
    have hinj : Function.Injective (aux_sb_LE (As s)) := by
      intro Y Z h
      exact aux_sb_L_inj (As s) (aux_sb_hom_hurwitz A hA s hs.1 hs.2) h
    have hsurj := LinearMap.injective_iff_surjective.mp hinj
    let e := (LinearEquiv.ofBijective (aux_sb_LE (As s)) ⟨hinj, hsurj⟩).toContinuousLinearEquiv
    refine ⟨ContinuousLinearEquiv.toUnit e, ?_⟩
    ext1 Y
    rfl
  set w : Fin n → Fin n → ℝ := -(Matrix.of.symm W) with hw
  set Xs : ℝ → Matrix (Fin n) (Fin n) ℝ :=
    fun s => Matrix.of (Ring.inverse (Lc s) w) with hXs
  have hXs_spec : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (As s).transpose * Xs s + Xs s * As s + W = 0 := by
    intro s hs
    obtain ⟨u, hu⟩ := hunit s hs
    have h1 : Lc s (Ring.inverse (Lc s) w) = w := by
      rw [← hu, Ring.inverse_unit]
      show ((u : (Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ)) * ↑u⁻¹) w = w
      rw [Units.mul_inv]; rfl
    have h2 : (As s).transpose * Xs s + Xs s * As s = -W := h1
    rw [h2, neg_add_cancel]
  have hXs_cont : ∀ s ∈ Set.Icc (0 : ℝ) 1, ContinuousAt Xs s := by
    intro s hs
    obtain ⟨u, hu⟩ := hunit s hs
    have h1 : ContinuousAt (fun t => Ring.inverse (Lc t)) s := by
      have := NormedRing.inverse_continuousAt u
      rw [hu] at this
      exact this.comp hLc_cont.continuousAt
    exact h1.clm_apply continuousAt_const
  set pr : ℝ → ℝ := fun s => (Set.projIcc (0 : ℝ) 1 zero_le_one s : ℝ) with hpr
  have hpr_cont : Continuous pr := continuous_subtype_val.comp continuous_projIcc
  have hpr_mem : ∀ s, pr s ∈ Set.Icc (0 : ℝ) 1 := fun s => Subtype.prop _
  have hpr_id : ∀ s ∈ Set.Icc (0 : ℝ) 1, pr s = s := by
    intro s hs; simp only [hpr, Set.projIcc_of_mem _ hs]
  set Xp : ℝ → Matrix (Fin n) (Fin n) ℝ := fun s => Xs (pr s) with hXp
  have hXp_cont : Continuous Xp := by
    rw [continuous_iff_continuousAt]
    intro s
    exact (hXs_cont (pr s) (hpr_mem s)).comp hpr_cont.continuousAt
  set Φ : ℝ → (Fin n → ℝ) → ℝ := fun s v => v ⬝ᵥ (Xp s *ᵥ v) with hΦ
  have hΦ_cont : Continuous ↿Φ := by
    show Continuous fun p : ℝ × (Fin n → ℝ) => p.2 ⬝ᵥ (Xp p.1 *ᵥ p.2)
    exact continuous_snd.dotProduct ((hXp_cont.comp continuous_fst).matrix_mulVec continuous_snd)
  have hΦs : ∀ s, Continuous (Φ s) := fun s => hΦ_cont.comp (Continuous.prodMk_right s)
  set K : Set (Fin n → ℝ) := Metric.sphere 0 1 with hK
  have hKc : IsCompact K := isCompact_sphere 0 1
  have hKne : K.Nonempty := (NormedSpace.sphere_nonempty).mpr zero_le_one
  set m : ℝ → ℝ := fun s => sInf (Φ s '' K) with hm
  have hm_cont : Continuous m := hKc.continuous_sInf hΦ_cont
  have hm_le : ∀ s, ∀ v ∈ K, m s ≤ Φ s v := fun s v hv =>
    csInf_le (hKc.bddBelow_image (hΦs s).continuousOn) (Set.mem_image_of_mem _ hv)
  have hm_att : ∀ s, ∃ v ∈ K, Φ s v = m s := fun s =>
    (hKc.image (hΦs s)).sInf_mem (hKne.image _)
  have hK_ne0 : ∀ v ∈ K, v ≠ 0 := by
    intro v hv h0
    rw [hK, mem_sphere_zero_iff_norm, h0, norm_zero] at hv
    exact zero_ne_one hv
  have hscale : ∀ v : Fin n → ℝ, v ≠ 0 → ‖v‖⁻¹ • v ∈ K := by
    intro v hv
    rw [hK, mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  -- value at 0
  have hAs0 : As 0 = A := by simp [hAs]
  have hXp0 : Xp 0 = X := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have e1 : Xp 0 = Xs 0 := by simp only [hXp, hpr_id 0 h0]
    have := hXs_spec 0 h0
    rw [hAs0] at this
    obtain ⟨Z, _, hZ⟩ := aux_sb_exists_unique A hA W
    rw [e1, hZ _ this, hZ _ hX]
  have hm0 : m 0 < 0 := by
    have hu := hscale v0 hv0ne
    have := hm_le 0 _ hu
    have e : Φ 0 (‖v0‖⁻¹ • v0) = (‖v0‖⁻¹) ^ 2 * (v0 ⬝ᵥ (X *ᵥ v0)) := by
      simp only [hΦ, hXp0]; exact aux_sb_quad_scale X _ v0
    have hpos : 0 < (‖v0‖⁻¹) ^ 2 := by
      have : 0 < ‖v0‖ := norm_pos_iff.mpr hv0ne
      positivity
    have : (‖v0‖⁻¹) ^ 2 * (v0 ⬝ᵥ (X *ᵥ v0)) < 0 := mul_neg_of_pos_of_neg hpos hv0
    linarith
  -- value at 1
  have hAs1 : As 1 = -1 := by simp [hAs]
  have hXp1 : Xp 1 = (1 / 2 : ℝ) • W := by
    have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have e1 : Xp 1 = Xs 1 := by simp only [hXp, hpr_id 1 h1]
    have := hXs_spec 1 h1
    rw [hAs1] at this
    simp only [Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mul, Matrix.one_mul,
      Matrix.mul_neg, Matrix.mul_one] at this
    rw [e1]
    have h2 : (2 : ℝ) • Xs 1 = W := by
      rw [two_smul]
      have h3 : W - (Xs 1 + Xs 1) = -Xs 1 + -Xs 1 + W := by abel
      rw [eq_comm, ← sub_eq_zero, h3, this]
    rw [← h2, smul_smul]; norm_num
  have hm1 : 0 < m 1 := by
    obtain ⟨v, hv, hvm⟩ := hm_att 1
    rw [← hvm]
    simp only [hΦ, hXp1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have := hW v (hK_ne0 v hv)
    positivity
  -- IVT
  obtain ⟨s, hs, hms⟩ := intermediate_value_Icc zero_le_one hm_cont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (m 0) (m 1) from ⟨hm0.le, hm1.le⟩)
  obtain ⟨v, hvK, hvm⟩ := hm_att s
  set Y := Xp s with hY
  have hYs : Y = Xs s := by simp only [hY, hXp, hpr_id s hs]
  have hYspec : (As s).transpose * Y + Y * As s + W = 0 := by rw [hYs]; exact hXs_spec s hs
  have hYsym : Y.transpose = Y :=
    aux_sb_symm (As s) (aux_sb_hom_hurwitz A hA s hs.1 hs.2) W Y hWs hYspec
  have hYpsd : ∀ u : Fin n → ℝ, 0 ≤ u ⬝ᵥ (Y *ᵥ u) := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    have h1 := hm_le s _ (hscale u hu)
    rw [hms] at h1
    have e : Φ s (‖u‖⁻¹ • u) = (‖u‖⁻¹) ^ 2 * (u ⬝ᵥ (Y *ᵥ u)) := by
      simp only [hΦ]; exact aux_sb_quad_scale Y _ u
    rw [e] at h1
    have hpos : 0 < (‖u‖⁻¹) ^ 2 := by
      have : 0 < ‖u‖ := norm_pos_iff.mpr hu
      positivity
    exact (mul_nonneg_iff_of_pos_left hpos).mp h1
  have hvY : v ⬝ᵥ (Y *ᵥ v) = 0 := by rw [← hms, ← hvm]
  have hPSD : Y.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hYsym]
    · intro x; simpa using hYpsd x
  have hYv : Y *ᵥ v = 0 := (hPSD.dotProduct_mulVec_zero_iff v).mp (by simpa using hvY)
  have := aux_sb_Y_zero (As s) Y W hYsym hYspec v hYv
  exact (hW v (hK_ne0 v hvK)).ne' this



lemma aux_sb_pd_lb {k : ℕ} (P : Matrix (Fin k) (Fin k) ℝ)
    (hP : ∀ v : Fin k → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (P *ᵥ v)) :
    ∃ c > 0, ∀ v : Fin k → ℝ, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (P *ᵥ v) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, one_pos, fun v => by simp [dotProduct]⟩
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hK : IsCompact (Metric.sphere (0 : Fin k → ℝ) 1) := isCompact_sphere 0 1
  have hKne : (Metric.sphere (0 : Fin k → ℝ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hq : Continuous fun v : Fin k → ℝ => v ⬝ᵥ (P *ᵥ v) :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  obtain ⟨v1, hv1, hmin⟩ := hK.exists_isMinOn hKne hq.continuousOn
  have hv1ne : v1 ≠ 0 := by
    intro h0
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hv1
    exact zero_ne_one hv1
  set μ := v1 ⬝ᵥ (P *ᵥ v1) with hμdef
  have hμ : 0 < μ := hP v1 hv1ne
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  refine ⟨μ / k, by positivity, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : Fin k → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']
  have h1 : μ ≤ (‖v‖⁻¹ • v) ⬝ᵥ (P *ᵥ (‖v‖⁻¹ • v)) := hmin hu
  rw [aux_sb_quad_scale] at h1
  have h2 : v ⬝ᵥ v ≤ k * ‖v‖ ^ 2 := by
    simp only [dotProduct]
    calc ∑ i, v i * v i ≤ ∑ _i : Fin k, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => by
          have := norm_le_pi_norm v i
          rw [Real.norm_eq_abs] at this
          nlinarith [abs_nonneg (v i), abs_mul_abs_self (v i)]
      _ = k * ‖v‖ ^ 2 := by simp
  have h3 : μ * ‖v‖ ^ 2 ≤ v ⬝ᵥ (P *ᵥ v) := by
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖v‖)
    calc μ * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ ^ 2 * (v ⬝ᵥ (P *ᵥ v)) * ‖v‖ ^ 2 := this
      _ = v ⬝ᵥ (P *ᵥ v) := by field_simp
  calc μ / k * (v ⬝ᵥ v) ≤ μ / k * (k * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = μ * ‖v‖ ^ 2 := by field_simp
    _ ≤ _ := h3

lemma aux_sb_bil {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Pi.single i (1 : ℝ) ⬝ᵥ (X *ᵥ Pi.single j 1) = X i j := by
  simp

lemma aux_sb_entry {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hXs : X.transpose = X)
    (hX : ∀ v, 0 ≤ v ⬝ᵥ (X *ᵥ v)) (i j : Fin n) : 2 * |X i j| ≤ X i i + X j j := by
  have hji : X j i = X i j := by
    have := congrFun (congrFun hXs i) j
    simpa [Matrix.transpose_apply] using this
  have h1 := hX (Pi.single i 1 + Pi.single j 1)
  have h2 := hX (Pi.single i 1 - Pi.single j 1)
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, add_dotProduct,
    dotProduct_sub, sub_dotProduct, aux_sb_bil] at h1 h2
  rcases abs_cases (X i j) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

lemma aux_sb_diag {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ v, 0 ≤ v ⬝ᵥ (X *ᵥ v)) (i : Fin n) : 0 ≤ X i i := by
  have := hX (Pi.single i 1)
  rwa [aux_sb_bil] at this

lemma aux_sb_trace_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : ∀ v, 0 ≤ v ⬝ᵥ (X *ᵥ v)) : 0 ≤ X.trace :=
  Finset.sum_nonneg fun i _ => aux_sb_diag X hX i

lemma aux_sb_entry_le {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hXs : X.transpose = X)
    (hX : ∀ v, 0 ≤ v ⬝ᵥ (X *ᵥ v)) (i j : Fin n) : |X i j| ≤ X.trace := by
  have h1 := aux_sb_entry X hXs hX i j
  have hi : X i i ≤ X.trace :=
    Finset.single_le_sum (f := fun k => X k k) (fun k _ => aux_sb_diag X hX k)
      (Finset.mem_univ i)
  have hj : X j j ≤ X.trace :=
    Finset.single_le_sum (f := fun k => X k k) (fun k _ => aux_sb_diag X hX k)
      (Finset.mem_univ j)
  linarith

lemma aux_sb_trW {n : ℕ} (M X W : Matrix (Fin n) (Fin n) ℝ) (hXs : X.transpose = X)
    (hX : ∀ v, 0 ≤ v ⬝ᵥ (X *ᵥ v)) (h : M.transpose * X + X * M + W = 0) :
    W.trace ≤ 2 * (∑ i, ∑ j, |M i j|) * X.trace := by
  have hW : W = -(M.transpose * X + X * M) := eq_neg_of_add_eq_zero_right h
  have hent := aux_sb_entry_le X hXs hX
  rw [hW, Matrix.trace_neg, Matrix.trace_add]
  have e1 : (M.transpose * X).trace = ∑ i, ∑ k, M k i * X k i := by
    simp [Matrix.trace, Matrix.mul_apply]
  have e2 : (X * M).trace = ∑ i, ∑ k, M k i * X i k := by
    simp [Matrix.trace, Matrix.mul_apply, mul_comm]
  have hS : ∑ i, ∑ k, |M k i| * X.trace = (∑ i, ∑ j, |M i j|) * X.trace := by
    rw [Finset.sum_comm, Finset.sum_mul]
    simp [Finset.sum_mul]
  have b1 : -(∑ i, ∑ k, M k i * X k i) ≤ (∑ i, ∑ j, |M i j|) * X.trace := by
    rw [← hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    calc -(M k i * X k i) ≤ |M k i * X k i| := neg_le_abs _
      _ = |M k i| * |X k i| := abs_mul _ _
      _ ≤ |M k i| * X.trace := mul_le_mul_of_nonneg_left (hent k i) (abs_nonneg _)
  have b2 : -(∑ i, ∑ k, M k i * X i k) ≤ (∑ i, ∑ j, |M i j|) * X.trace := by
    rw [← hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    calc -(M k i * X i k) ≤ |M k i * X i k| := neg_le_abs _
      _ = |M k i| * |X i k| := abs_mul _ _
      _ ≤ |M k i| * X.trace := mul_le_mul_of_nonneg_left (hent i k) (abs_nonneg _)
  rw [e1, e2]
  linarith

lemma aux_sb_tr_vmv {n : ℕ} (u : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :
    (vecMulVec u (star u) * P).trace = u ⬝ᵥ (P *ᵥ u) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, star_trivial,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma aux_sb_trXS {n : ℕ} (X S : Matrix (Fin n) (Fin n) ℝ) (hXs : X.transpose = X)
    (hX : ∀ v, 0 ≤ v ⬝ᵥ (X *ᵥ v)) (c : ℝ) (hS : ∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v)) :
    c * X.trace ≤ (X * S).trace := by
  have hpsd : X.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hXs]
    · intro x; simpa using hX x
  obtain ⟨k, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hpsd
  rw [hv, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := aux_sb_tr_vmv (v i) S
  have h2 : (vecMulVec (v i) (star (v i))).trace = v i ⬝ᵥ v i := by
    simp
  rw [h1, h2]
  exact hS (v i)

lemma aux_sb_quad_conj {p q : ℕ} (G : Matrix (Fin p) (Fin q) ℝ) (P : Matrix (Fin p) (Fin p) ℝ)
    (v : Fin q → ℝ) :
    v ⬝ᵥ ((G.transpose * P * G) *ᵥ v) = (G *ᵥ v) ⬝ᵥ (P *ᵥ (G *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

lemma aux_sb_tr_conj {p q : ℕ} (G : Matrix (Fin p) (Fin q) ℝ) (P : Matrix (Fin p) (Fin p) ℝ)
    (c : ℝ) (hP : ∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (P *ᵥ v)) :
    c * (∑ i, ∑ j, G i j ^ 2) ≤ (G.transpose * P * G).trace := by
  have e : ∀ j, (G.transpose * P * G) j j =
      (G *ᵥ Pi.single j 1) ⬝ᵥ (P *ᵥ (G *ᵥ Pi.single j 1)) := by
    intro j
    rw [← aux_sb_quad_conj, aux_sb_bil]
  have e2 : ∀ j, (G *ᵥ Pi.single j 1) ⬝ᵥ (G *ᵥ Pi.single j 1) = ∑ i, G i j ^ 2 := by
    intro j
    simp [dotProduct, sq]
  rw [Finset.sum_comm, Finset.mul_sum]
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [e j, ← e2 j]
  exact hP _

lemma aux_sb_rank_inj {n r : ℕ} (C : Matrix (Fin r) (Fin n) ℝ) (hC : C.rank = r)
    (u : Fin r → ℝ) (hu : C.transpose *ᵥ u = 0) : u = 0 := by
  have h1 : C.transpose.rank = r := by rw [Matrix.rank_transpose, hC]
  have h2 := LinearMap.finrank_range_add_finrank_ker (C.transpose.mulVecLin)
  rw [show Module.finrank ℝ (LinearMap.range C.transpose.mulVecLin) = C.transpose.rank from rfl,
    h1, Module.finrank_fin_fun] at h2
  have h3 : Module.finrank ℝ (LinearMap.ker C.transpose.mulVecLin) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at h3
  have : u ∈ LinearMap.ker C.transpose.mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hu
  rw [h3] at this
  simpa using this

lemma aux_sb_l1_mul {a b c : ℕ} (P : Matrix (Fin a) (Fin b) ℝ) (Q : Matrix (Fin b) (Fin c) ℝ) :
    ∑ i, ∑ j, |(P * Q) i j| ≤ (∑ i, ∑ k, |P i k|) * (∑ k, ∑ j, |Q k j|) := by
  calc ∑ i, ∑ j, |(P * Q) i j| ≤ ∑ i, ∑ j, ∑ k, |P i k| * |Q k j| := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        simp [abs_mul]
    _ = ∑ i, ∑ k, |P i k| * (∑ j, |Q k j|) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        simp [Finset.mul_sum]
    _ ≤ ∑ i, ∑ k, |P i k| * (∑ k', ∑ j, |Q k' j|) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact Finset.single_le_sum (f := fun k' => ∑ j, |Q k' j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    _ = _ := by rw [Finset.sum_mul]; simp [Finset.sum_mul]

lemma aux_sb_entry_le_frob {m r : ℕ} (K : Matrix (Fin m) (Fin r) ℝ) (i : Fin m) (j : Fin r) :
    |K i j| ≤ frobNorm K := by
  unfold frobNorm
  apply Real.abs_le_sqrt
  have h1 : K i j ^ 2 ≤ ∑ j', K i j' ^ 2 :=
    Finset.single_le_sum (f := fun j' => K i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', K i j' ^ 2 ≤ ∑ i', ∑ j', K i' j' ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', K i' j' ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  linarith


lemma aux_sb_arith (c α β F N : ℝ) (hc : 0 < c) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hF : 0 ≤ F)
    (_hN : 0 ≤ N) (h : c * N ^ 2 ≤ 2 * (α + β * N) * F) :
    N ≤ 1 + 2 * (α + β) * |F| / c := by
  rw [abs_of_nonneg hF]
  have hq0 : 0 ≤ 2 * (α + β) * F / c := by positivity
  rcases le_or_gt N 1 with hN1 | hN1
  · linarith
  · have h6 : c * N ≤ 2 * (α + β) * F := by
      have h7 : c * N ^ 2 ≤ 2 * (α + β) * F * N := by
        have : 2 * (α + β * N) * F ≤ 2 * (α + β) * F * N := by
          have : α ≤ α * N := by nlinarith
          nlinarith
        linarith
      have hNpos : 0 < N := by linarith
      nlinarith
    have h7 : N ≤ 2 * (α + β) * F / c := by
      rw [le_div_iff₀ hc]; linarith
    linarith

lemma aux_sb_main {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) :
    ∃ M : ℝ, ∀ K ∈ sublevel A B C Q R Sig K₀, frobNorm K ≤ M := by
  obtain ⟨cS, hcS, hS⟩ := aux_sb_pd_lb Sig (fun v hv => by
    simpa using hSig.dotProduct_mulVec_pos hv)
  obtain ⟨cR, hcR, hRl⟩ := aux_sb_pd_lb R (fun v hv => by
    simpa using hR.dotProduct_mulVec_pos hv)
  obtain ⟨cC, hcC, hCl⟩ := aux_sb_pd_lb (C * C.transpose) (fun u hu => by
    have hw : C.transpose *ᵥ u ≠ 0 := fun h => hu (aux_sb_rank_inj C hC u h)
    have e : u ⬝ᵥ ((C * C.transpose) *ᵥ u) = (C.transpose *ᵥ u) ⬝ᵥ (C.transpose *ᵥ u) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [e]
    refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg _) ?_
    intro h
    exact hw (dotProduct_self_eq_zero.mp h.symm))
  have hRt : R.transpose = R := by
    have := hR.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hQt : Q.transpose = Q := by
    have := hQ.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hQpsd : ∀ v, 0 ≤ v ⬝ᵥ (Q *ᵥ v) := fun v => by
    simpa using hQ.posSemidef.dotProduct_mulVec_nonneg v
  have hRpsd : ∀ v, 0 ≤ v ⬝ᵥ (R *ᵥ v) := fun v => by
    simpa using hR.posSemidef.dotProduct_mulVec_nonneg v
  obtain ⟨F, hF⟩ : ∃ F, lqrCost A B C Q R Sig K₀ = F := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : ℝ, ∑ i, ∑ j, |A i j| = α := ⟨_, rfl⟩
  have hB0 : 0 ≤ ∑ i, ∑ k, |B i k| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC0 : 0 ≤ ∑ k, ∑ j, |C k j| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨β, hβ⟩ : ∃ β : ℝ,
    (∑ i, ∑ k, |B i k|) * (∑ k, ∑ j, |C k j|) * ((m : ℝ) * r) = β := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := hα ▸ Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hβ0 : 0 ≤ β := by rw [← hβ]; positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, cC * cR * cS = c := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [← hc]; positivity
  refine ⟨1 + 2 * (α + β) * |F| / c, fun K hK => ?_⟩
  obtain ⟨hKs, hKF⟩ := hK
  rw [hF] at hKF
  obtain ⟨N, hNdef⟩ : ∃ N, frobNorm K = N := ⟨_, rfl⟩
  have hN0 : 0 ≤ N := hNdef ▸ Real.sqrt_nonneg _
  have hN2 : N ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
    rw [← hNdef]
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [hNdef]
  have hAKH : IsHurwitz (A - B * K * C) := hKs
  have hX := aux_sb_lyapSol_spec (A - B * K * C) hAKH
    (C.transpose * K.transpose * R * K * C + Q)
  have hfK : lqrCost A B C Q R Sig K = (lyapSol (A - B * K * C)
      (C.transpose * K.transpose * R * K * C + Q) * Sig).trace := rfl
  rw [hfK] at hKF
  generalize lyapSol (A - B * K * C) (C.transpose * K.transpose * R * K * C + Q) = X at hX hKF
  generalize hAK : A - B * K * C = AK at hX hAKH
  generalize hWK : C.transpose * K.transpose * R * K * C + Q = WK at hX
  have hWt : WK.transpose = WK := by
    rw [← hWK]
    simp only [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, hRt,
      hQt, Matrix.mul_assoc]
  have hGt : C.transpose * K.transpose * R * K * C = (K * C).transpose * R * (K * C) := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hWpd : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (WK *ᵥ v) := by
    intro v hv
    rw [← hWK, Matrix.add_mulVec, dotProduct_add, hGt, aux_sb_quad_conj]
    have h1 := hRpsd ((K * C) *ᵥ v)
    have h2 := hQ.dotProduct_mulVec_pos hv
    simp only [star_trivial] at h2
    linarith
  have hXpsd := aux_sb_psd AK WK X hAKH hWt hWpd hX
  have hXs := aux_sb_symm AK hAKH WK X hWt hX
  have hT : 0 ≤ X.trace := aux_sb_trace_nonneg X hXpsd
  have h1 : cS * X.trace ≤ (X * Sig).trace := aux_sb_trXS X Sig hXs hXpsd cS hS
  have h1' : cS * X.trace ≤ F := le_trans h1 hKF
  have hF0 : 0 ≤ F := le_trans (mul_nonneg hcS.le hT) h1'
  have h2 : WK.trace ≤ 2 * (∑ i, ∑ j, |AK i j|) * X.trace := aux_sb_trW AK X WK hXs hXpsd hX
  have h3 : cR * (∑ i, ∑ j, (K * C) i j ^ 2) ≤ WK.trace := by
    have e : WK.trace = ((K * C).transpose * R * (K * C)).trace + Q.trace := by
      rw [← hWK, Matrix.trace_add, hGt]
    have hQtr : 0 ≤ Q.trace := aux_sb_trace_nonneg Q hQpsd
    have := aux_sb_tr_conj (K * C) R cR hRl
    linarith
  have h4 : cC * N ^ 2 ≤ ∑ i, ∑ j, (K * C) i j ^ 2 := by
    rw [hN2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have e1 : ∑ j, (K * C) i j ^ 2 = (C.transpose *ᵥ K i) ⬝ᵥ (C.transpose *ᵥ K i) := by
      simp only [dotProduct, sq]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : (K * C) i j = (C.transpose *ᵥ K i) j := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
      rw [this]
    have e2 : K i ⬝ᵥ ((C * C.transpose) *ᵥ K i) =
        (C.transpose *ᵥ K i) ⬝ᵥ (C.transpose *ᵥ K i) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have e3 : K i ⬝ᵥ K i = ∑ j, K i j ^ 2 := by simp [dotProduct, sq]
    rw [e1, ← e2, ← e3]
    exact hCl (K i)
  have h5 : ∑ i, ∑ j, |AK i j| ≤ α + β * N := by
    have hK1 : ∑ i, ∑ j, |K i j| ≤ (m : ℝ) * r * N := by
      calc ∑ i, ∑ j, |K i j| ≤ ∑ _i : Fin m, ∑ _j : Fin r, N :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              hNdef ▸ aux_sb_entry_le_frob K i j
        _ = (m : ℝ) * r * N := by simp [Finset.sum_const]; ring
    have hBKC : ∑ i, ∑ j, |(B * K * C) i j| ≤ β * N := by
      have hb1 := aux_sb_l1_mul (B * K) C
      have hb2 := aux_sb_l1_mul B K
      calc ∑ i, ∑ j, |(B * K * C) i j|
          ≤ (∑ i, ∑ k, |(B * K) i k|) * (∑ k, ∑ j, |C k j|) := hb1
        _ ≤ ((∑ i, ∑ k, |B i k|) * (∑ k, ∑ j, |K k j|)) * (∑ k, ∑ j, |C k j|) :=
            mul_le_mul_of_nonneg_right hb2 hC0
        _ ≤ ((∑ i, ∑ k, |B i k|) * ((m : ℝ) * r * N)) * (∑ k, ∑ j, |C k j|) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK1 hB0) hC0
        _ = β * N := by rw [← hβ]; ring
    calc ∑ i, ∑ j, |AK i j| ≤ ∑ i, ∑ j, (|A i j| + |(B * K * C) i j|) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [← hAK, Matrix.sub_apply]
          exact abs_sub _ _
      _ = α + ∑ i, ∑ j, |(B * K * C) i j| := by
          simp only [Finset.sum_add_distrib, hα]
      _ ≤ α + β * N := by linarith
  have haK0 : 0 ≤ ∑ i, ∑ j, |AK i j| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hmain : c * N ^ 2 ≤ 2 * (α + β * N) * F := by
    have s1 : c * N ^ 2 ≤ cR * cS * (∑ i, ∑ j, (K * C) i j ^ 2) := by
      calc c * N ^ 2 = cR * cS * (cC * N ^ 2) := by rw [← hc]; ring
        _ ≤ cR * cS * (∑ i, ∑ j, (K * C) i j ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (mul_pos hcR hcS).le
    have s2 : cR * cS * (∑ i, ∑ j, (K * C) i j ^ 2) ≤ cS * WK.trace := by
      calc cR * cS * (∑ i, ∑ j, (K * C) i j ^ 2)
          = cS * (cR * (∑ i, ∑ j, (K * C) i j ^ 2)) := by ring
        _ ≤ cS * WK.trace := mul_le_mul_of_nonneg_left h3 hcS.le
    have s3 : cS * WK.trace ≤ 2 * (∑ i, ∑ j, |AK i j|) * (cS * X.trace) := by
      calc cS * WK.trace ≤ cS * (2 * (∑ i, ∑ j, |AK i j|) * X.trace) :=
            mul_le_mul_of_nonneg_left h2 hcS.le
        _ = 2 * (∑ i, ∑ j, |AK i j|) * (cS * X.trace) := by ring
    have s4 : 2 * (∑ i, ∑ j, |AK i j|) * (cS * X.trace) ≤ 2 * (∑ i, ∑ j, |AK i j|) * F :=
      mul_le_mul_of_nonneg_left h1' (mul_nonneg zero_le_two haK0)
    have s5 : 2 * (∑ i, ∑ j, |AK i j|) * F ≤ 2 * (α + β * N) * F :=
      mul_le_mul_of_nonneg_right (by linarith) hF0
    linarith
  exact aux_sb_arith c α β F N hc0 hα0 hβ0 hF0 hN0 hmain

end FatkhullinPolyak.Discrete

open FatkhullinPolyak.Discrete

theorem solution {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) (hK₀ : K₀ ∈ stabSet A B C) :
    ∃ M : ℝ, ∀ K ∈ sublevel A B C Q R Sig K₀, frobNorm K ≤ M :=
  aux_sb_main A B C Q R Sig hQ hR hSig hC K₀
