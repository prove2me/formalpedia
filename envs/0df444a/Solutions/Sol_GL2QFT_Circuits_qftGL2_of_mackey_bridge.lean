-- Prove2me | solution 1 for GL2QFT.Circuits.qftGL2_of_mackey_bridge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T07:01:41.010934+00:00
-- url     : https://prove2.me/submissions/78bbd05c-575f-47ed-ac80-62cdd3669a37
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GL2QFT_Circuits_Leaves
import Theorems.Thm_GL2QFT_Circuits_qftGL2_eq_mackey_factorization
import Theorems.Thm_GL2QFT_Circuits_mackeyEnc_uniform
import Theorems.Thm_GL2QFT_Circuits_mackeyNop_uniform
import Theorems.Thm_GL2QFT_Circuits_mackeyReindex_uniform
import Theorems.Thm_GL2QFT_Circuits_fieldWidths_poly
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_frame
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_restrict
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_seq
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_eq

open Classical
noncomputable section

namespace GL2QFT_MackeyBridge_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.FieldData GL2QFT.Supplement.TotalA QAlgorithms

lemma norm_mulVec_le_of_iso {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    (M : Matrix Y X ℂ) (hM : M.conjTranspose * M = 1) (ψ : EuclideanSpace ℂ X) :
    ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))‖ ≤ ‖ψ‖ := by
  have hnorm_sq : ∀ {ι : Type} [Fintype ι] (v : ι → ℂ),
      ((∑ i : ι, ‖v i‖ ^ 2 : ℝ) : ℂ) = ∑ i : ι, star (v i) * v i := by
    intro ι _ v
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self,
      RCLike.star_def, mul_comm]
  have hlhs_c : ((‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))‖ ^ 2 : ℝ) : ℂ) =
      ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, hnorm_sq, hnorm_sq]
    simp_rw [Matrix.mulVec, dotProduct, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x₁ _ => ?_
    rw [Finset.sum_comm]
    have hx : ∀ x₂ : X, (∑ y : Y, star (ψ x₁) * star (M y x₁) * (M y x₂ * ψ x₂)) =
        star (ψ x₁) * ((∑ y : Y, star (M y x₁) * M y x₂) * ψ x₂) := by
      intro x₂
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => by ring
    simp_rw [hx]
    have hinner : ∀ x₂ : X, (∑ y : Y, star (M y x₁) * M y x₂) = (1 : Matrix X X ℂ) x₁ x₂ := by
      intro x₂
      have := congrFun (congrFun hM x₁) x₂
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using this
    simp_rw [hinner, Matrix.one_apply]
    simp
  have hsq : ‖WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))‖ ^ 2 = ‖ψ‖ ^ 2 :=
    Complex.ofReal_injective hlhs_c
  nlinarith [norm_nonneg (WithLp.toLp 2 (M.mulVec (WithLp.ofLp ψ))), norm_nonneg ψ]

lemma isometry_mul {X M Y : Type} [Fintype X] [DecidableEq X] [Fintype M] [DecidableEq M] [Fintype Y]
    {A : Matrix M X ℂ} {B : Matrix Y M ℂ}
    (hA : A.conjTranspose * A = 1) (hB : B.conjTranspose * B = 1) :
    (B * A).conjTranspose * (B * A) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B.conjTranspose B A, hB,
    Matrix.one_mul, hA]

lemma frameMat_iso {A X Y : Type} [Fintype A] [DecidableEq A] [Fintype X] [DecidableEq X] [Fintype Y]
    {M : Matrix Y X ℂ} (hM : M.conjTranspose * M = 1) :
    (frameMat (A := A) M).conjTranspose * frameMat (A := A) M = 1 := by
  ext i j
  simp only [frameMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  dsimp only
  by_cases hij : i.1 = j.1
  · have hsum : (∑ a : A, ∑ y : Y, star (if a = i.1 then M y i.2 else 0) *
        (if a = j.1 then M y j.2 else 0)) = ∑ y : Y, star (M y i.2) * M y j.2 := by
      rw [Finset.sum_eq_single i.1]
      · simp [hij]
      · intro a _ ha; simp [ha]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [hsum]
    have hm := congrFun (congrFun hM i.2) j.2
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
    rw [hm]
    simp [hij, Prod.ext_iff]
  · rw [Finset.sum_eq_zero]
    · simp [Prod.ext_iff, hij]
    · intro a _; rw [Finset.sum_eq_zero]; intro y _
      by_cases ha : a = i.1
      · subst ha; simp [hij]
      · simp [ha]

lemma submatrix_iso {X Y X' Y' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Fintype X'] [DecidableEq X'] [Fintype Y']
    (M : Matrix Y X ℂ) (hM : M.conjTranspose * M = 1)
    (ιX : X' → X) (ιY : Y' → Y)
    (hιX : Function.Injective ιX) (hιY : Function.Injective ιY)
    (hinv : ∀ x' y, (∀ y', ιY y' ≠ y) → M y (ιX x') = 0) :
    (M.submatrix ιY ιX).conjTranspose * (M.submatrix ιY ιX) = 1 := by
  ext x₁' x₂'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.one_apply]
  have himg : (∑ y' : Y', star (M (ιY y') (ιX x₁')) * M (ιY y') (ιX x₂')) =
      ∑ y ∈ Finset.univ.image ιY, star (M y (ιX x₁')) * M y (ιX x₂') := by
    rw [Finset.sum_image]
    intro y₁ _ y₂ _ hy; exact hιY hy
  rw [himg]
  have hfull : (∑ y ∈ Finset.univ.image ιY, star (M y (ιX x₁')) * M y (ιX x₂')) =
      ∑ y : Y, star (M y (ιX x₁')) * M y (ιX x₂') := by
    refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
    have hnone : ∀ y', ιY y' ≠ y := fun y' h => hy (Finset.mem_image.mpr ⟨y', Finset.mem_univ _, h⟩)
    simp [hinv x₁' y hnone]
  rw [hfull]
  have hm := congrFun (congrFun hM (ιX x₁')) (ιX x₂')
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
  rw [hm]
  simp [hιX.eq_iff]

lemma tagCode_inl_injective (D : FieldData) : Function.Injective (fun a : D.Fq => D.tagCode (.inl a)) := by
  intro a₁ a₂ h
  have hq : 2 ≤ D.q := D.one_lt_q
  have hqsq : 2 < D.q ^ 2 := by nlinarith
  have hlabW_pos : 0 < D.labW := Nat.clog_pos (by norm_num) (by omega)
  have hp_pos : 0 < D.p := D.hp.pos
  have : NeZero D.p := ⟨D.hp.ne_zero⟩
  have hlt2pow : D.p < 2 ^ D.labW := by
    have hpow : D.q ^ 2 ≤ 2 ^ D.labW := Nat.le_pow_clog (by norm_num) _
    have hpq : D.p ≤ D.q := Nat.le_self_pow D.hr.ne' D.p
    have : D.q < D.q ^ 2 := by nlinarith
    omega
  have hdig : ∀ l : ℕ, l < D.r → D.digit a₁ l = D.digit a₂ l := by
    intro l hl
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < D.labW
    · have hidx : (l + 1) * D.labW + k < (D.r + 1) * D.labW := by nlinarith
      have hb := congr_fun h ⟨(l + 1) * D.labW + k, hidx⟩
      have hdiv : ((l + 1) * D.labW + k) / D.labW = l + 1 := by
        rw [Nat.mul_comm (l + 1) D.labW, Nat.mul_add_div hlabW_pos, Nat.div_eq_of_lt hk, add_zero]
      have hmod : ((l + 1) * D.labW + k) % D.labW = k := by
        rw [Nat.mul_comm (l + 1) D.labW, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
      simpa [tagCode, packNat, hdiv, hmod] using hb
    · have hk1 : D.digit a₁ l < 2 ^ k := lt_of_lt_of_le (lt_trans (ZMod.val_lt _) hlt2pow)
        (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hk))
      have hk2 : D.digit a₂ l < 2 ^ k := lt_of_lt_of_le (lt_trans (ZMod.val_lt _) hlt2pow)
        (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hk))
      rw [Nat.testBit_lt_two_pow hk1, Nat.testBit_lt_two_pow hk2]
  have hcoeff_ge : ∀ a : D.Fq, ∀ l : ℕ, D.r ≤ l →
      (AdjoinRoot.modByMonicHom D.f_monic a).coeff l = 0 := by
    intro a l hl
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [AdjoinRoot.modByMonicHom_mk D.f_monic p]
    by_cases hpz : p %ₘ D.f = 0
    · simp [hpz]
    · have hdeg := Polynomial.degree_modByMonic_lt p D.f_monic
      rw [Polynomial.degree_eq_natDegree hpz, Polynomial.degree_eq_natDegree D.f_monic.ne_zero,
        D.f_deg] at hdeg
      have hnat : (p %ₘ D.f).natDegree < D.r := WithBot.coe_lt_coe.mp hdeg
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hnat hl)
  have hpoly : AdjoinRoot.modByMonicHom D.f_monic a₁ = AdjoinRoot.modByMonicHom D.f_monic a₂ := by
    ext l
    by_cases hl : l < D.r
    · apply ZMod.val_injective
      exact hdig l hl
    · rw [hcoeff_ge a₁ l (le_of_not_gt hl), hcoeff_ge a₂ l (le_of_not_gt hl)]
  exact (AdjoinRoot.mk_leftInverse D.f_monic).injective hpoly

lemma cosetCode_injective (D : FieldData) : Function.Injective (cosetCode D) := by
  intro t₁ t₂ h
  cases t₁ with
  | inl u₁ =>
      cases t₂ with
      | inl u₂ => rfl
      | inr x₂ =>
          have h0 := congr_fun h (Fin.castAdd ((D.r + 1) * D.labW) (0 : Fin 1))
          simp only [cosetCode, boolAppCode, Fin.append_left] at h0
          exact absurd h0 (by decide)
  | inr x₁ =>
      cases t₂ with
      | inl u₂ =>
          have h0 := congr_fun h (Fin.castAdd ((D.r + 1) * D.labW) (0 : Fin 1))
          simp only [cosetCode, boolAppCode, Fin.append_left] at h0
          exact absurd h0 (by decide)
      | inr x₂ =>
          congr 1
          apply tagCode_inl_injective D
          funext i
          have hi := congr_fun h (Fin.natAdd 1 i)
          simpa only [cosetCode, boolAppCode, Fin.append_right] using hi

lemma labPairCode_injective (D : FieldData) :
    Function.Injective (fun p : D.Lab × D.Lab => packNat 2 D.labW ![p.1.val, p.2.val]) := by
  have hq : 2 ≤ D.q := D.one_lt_q
  have hqsq : 2 < D.q ^ 2 := by nlinarith
  have hlabW_pos : 0 < D.labW := Nat.clog_pos (by norm_num) (by omega)
  have : NeZero (D.q - 1) := ⟨by omega⟩
  have hlt2pow : D.q - 1 < 2 ^ D.labW := by
    have hpow : D.q ^ 2 ≤ 2 ^ D.labW := Nat.le_pow_clog (by norm_num) _
    have : D.q < D.q ^ 2 := by nlinarith
    omega
  have extract : ∀ {n₁ n₂ : ℕ}, n₁ < D.q - 1 → n₂ < D.q - 1 →
      (∀ k : ℕ, k < D.labW → Nat.testBit n₁ k = Nat.testBit n₂ k) → n₁ = n₂ := by
    intro n₁ n₂ h₁ h₂ hk
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hlt : k < D.labW
    · exact hk k hlt
    · have hb1 : n₁ < 2 ^ k := lt_of_lt_of_le (lt_trans h₁ hlt2pow)
        (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hlt))
      have hb2 : n₂ < 2 ^ k := lt_of_lt_of_le (lt_trans h₂ hlt2pow)
        (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hlt))
      rw [Nat.testBit_lt_two_pow hb1, Nat.testBit_lt_two_pow hb2]
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  have ha : a₁ = a₂ := by
    apply ZMod.val_injective
    apply extract (ZMod.val_lt a₁) (ZMod.val_lt a₂)
    intro k hk
    have hidx : k < 2 * D.labW := by omega
    have hb := congr_fun h ⟨k, hidx⟩
    have hdiv : k / D.labW = 0 := Nat.div_eq_of_lt hk
    have hmod : k % D.labW = k := Nat.mod_eq_of_lt hk
    simpa [packNat, hdiv, hmod, Matrix.cons_val_zero] using hb
  have hb : b₁ = b₂ := by
    apply ZMod.val_injective
    apply extract (ZMod.val_lt b₁) (ZMod.val_lt b₂)
    intro k hk
    have hidx : D.labW + k < 2 * D.labW := by omega
    have hb := congr_fun h ⟨D.labW + k, hidx⟩
    have hdiv : (D.labW + k) / D.labW = 1 := by
      rw [Nat.add_div_left _ hlabW_pos, Nat.div_eq_of_lt hk, zero_add]
    have hmod : (D.labW + k) % D.labW = k := by
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt hk]
    simpa [packNat, hdiv, hmod, Matrix.cons_val_one, Matrix.cons_val_fin_one] using hb
  exact Prod.ext ha hb

end GL2QFT_MackeyBridge_Aux

open Classical GL2QFT GL2QFT.Circuits GL2QFT.FieldData GL2QFT.Supplement.TotalA GL2QFT_MackeyBridge_Aux

theorem solution
    (hFB : UniformlyImplementsOn (fun _ => True) (fun D => D.bInCode) (fun D => D.bOutCode) (fun D => D.qftB))
    (hA : UniformlyImplementsOn (fun _ => True) (fun D => inCodeA D) (fun D => outCodeA D) (fun D => totalA D)) :
    UniformlyImplementsOn (fun _ => True) (fun D => D.inCode) (fun D => D.outCode) (fun D => D.qftGL2) := by
  have h2 := uniformlyImplementsOn_frame (cosetCode) hFB (fun D _ => cosetCode_injective D)
    (by
      obtain ⟨f, hf, hfeq⟩ := fieldWidths_poly.2.2.2.1
      exact ⟨f, hf, fun D _ => hfeq D⟩)
  have h4_frame := uniformlyImplementsOn_frame
    (fun D (p : D.Lab × D.Lab) => packNat 2 D.labW ![p.1.val, p.2.val]) hA
    (fun D _ => labPairCode_injective D)
    (by
      obtain ⟨f, hf, hfeq⟩ := fieldWidths_poly.2.2.2.2.1
      exact ⟨f, hf, fun D _ => hfeq D⟩)
  have h4 := uniformlyImplementsOn_restrict mackeyMidEmb mackeyOutEmb h4_frame
    (fun D _ => (qftGL2_eq_mackey_factorization D).2.2.2.2.2.2.1)
    (fun D _ => (qftGL2_eq_mackey_factorization D).2.2.2.2.2.2.2)
    (fun D _ x' y hy => (qftGL2_eq_mackey_factorization D).2.2.2.2.2.1 x' y hy)
  have h12 := uniformlyImplementsOn_seq mackeyEnc_uniform h2 fun D _ ψ =>
    norm_mulVec_le_of_iso _ (by convert (qftGL2_eq_mackey_factorization D).2.1) ψ
  have h123 := uniformlyImplementsOn_seq h12 mackeyNop_uniform fun D _ ψ =>
    norm_mulVec_le_of_iso _
      (isometry_mul (by convert (qftGL2_eq_mackey_factorization D).2.1)
        (frameMat_iso (by convert (qftGL2_eq_mackey_factorization D).2.2.1))) ψ
  have h1234 := uniformlyImplementsOn_seq h123 h4 fun D _ ψ =>
    norm_mulVec_le_of_iso _
      (isometry_mul
        (isometry_mul (by convert (qftGL2_eq_mackey_factorization D).2.1)
          (frameMat_iso (by convert (qftGL2_eq_mackey_factorization D).2.2.1)))
        (by convert (qftGL2_eq_mackey_factorization D).2.2.2.1)) ψ
  have h12345 := uniformlyImplementsOn_seq h1234 mackeyReindex_uniform fun D _ ψ => by
    have hA_iso : (totalA D).conjTranspose * totalA D = 1 := by
      convert (qftGL2_eq_mackey_factorization D).2.2.2.2.1
    have h4_frame_iso :
        (frameMat (A := D.Lab × D.Lab) (totalA D)).conjTranspose *
          frameMat (A := D.Lab × D.Lab) (totalA D) = 1 := by
      convert frameMat_iso hA_iso
    have h4_sub_iso :
        ((frameMat (A := D.Lab × D.Lab) (totalA D)).submatrix (mackeyOutEmb D) (mackeyMidEmb D)).conjTranspose *
          (frameMat (A := D.Lab × D.Lab) (totalA D)).submatrix (mackeyOutEmb D) (mackeyMidEmb D) = 1 := by
      convert submatrix_iso _ h4_frame_iso
        (mackeyMidEmb D) (mackeyOutEmb D)
        (qftGL2_eq_mackey_factorization D).2.2.2.2.2.2.1
        (qftGL2_eq_mackey_factorization D).2.2.2.2.2.2.2
        (qftGL2_eq_mackey_factorization D).2.2.2.2.2.1
    exact norm_mulVec_le_of_iso _
      (isometry_mul
        (isometry_mul
          (isometry_mul (by convert (qftGL2_eq_mackey_factorization D).2.1)
            (frameMat_iso (by convert (qftGL2_eq_mackey_factorization D).2.2.1)))
          (by convert (qftGL2_eq_mackey_factorization D).2.2.2.1))
        h4_sub_iso) ψ
  exact uniformlyImplementsOn_eq h12345 fun D _ => by
    rw [(qftGL2_eq_mackey_factorization D).1]
    simp only [Matrix.mul_assoc]
