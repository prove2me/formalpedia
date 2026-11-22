-- Prove2me | solution 1 for GL2QFT.theorem_6_13
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:34:59.706813+00:00
-- url     : https://prove2.me/submissions/8766f18d-3486-4c0d-b94a-ed6b16e03d01
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GL2QFT_Uniform
import Definitions.Def_GL2QFT_Circuits_Combinators
import Theorems.Thm_GL2QFT_lemma_6_8
import Theorems.Thm_GL2QFT_Circuits_phi_isometries
import Theorems.Thm_GL2QFT_Circuits_fieldWidths_poly
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_seq
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_eq
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_frame
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_frame_right
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_restrict
import Theorems.Thm_GL2QFT_Circuits_qftB_algebraic_factorization
import Theorems.Thm_GL2QFT_Circuits_perm_FB_out_uniform

open Classical
noncomputable section

namespace GL2QFT_Thm613_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.FieldData QAlgorithms

lemma card_Fq (D : FieldData) : Fintype.card D.Fq = D.q := by
  have hdim : Module.finrank (ZMod D.p) D.Fq = D.r := by
    rw [(AdjoinRoot.powerBasis' D.f_monic).finrank, AdjoinRoot.powerBasis'_dim, D.f_deg]
  have hc := Module.card_eq_pow_finrank (K := ZMod D.p) (V := D.Fq)
  rw [hdim, ZMod.card] at hc
  exact hc

lemma card_Fq2 (D : FieldData) : Fintype.card D.Fq2 = D.q ^ 2 := by
  have hdim : Module.finrank D.Fq D.Fq2 = 2 := by
    rw [(AdjoinRoot.powerBasis' D.F_monic).finrank, AdjoinRoot.powerBasis'_dim, D.F_deg]
  have hc := Module.card_eq_pow_finrank (K := D.Fq) (V := D.Fq2)
  rw [hdim, card_Fq] at hc
  exact hc

lemma algebraMap_gen (D : FieldData) : algebraMap D.Fq D.Fq2 D.gen = D.h ^ (D.q + 1) := by
  unfold gen
  have hnorm := @FiniteField.algebraMap_norm_eq_pow D.Fq D.Fq2 _ _ _ _ D.h
  rw [hnorm, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_Fq2, card_Fq]
  have hq : 1 < D.q := D.one_lt_q
  have hsq : D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by
    zify [Nat.le_of_lt hq, show 1 ≤ D.q ^ 2 by nlinarith]; ring
  rw [hsq, Nat.mul_div_cancel _ (by omega)]

lemma orderOf_gen (D : FieldData) : orderOf D.gen = D.q - 1 := by
  let f : D.Fq →* D.Fq2 := (algebraMap D.Fq D.Fq2).toMonoidHom
  have hf : Function.Injective f := (algebraMap D.Fq D.Fq2).injective
  rw [← orderOf_injective f hf D.gen]
  change orderOf (algebraMap D.Fq D.Fq2 D.gen) = D.q - 1
  rw [algebraMap_gen, orderOf_pow' D.h (by omega), D.h_order]
  change (D.q ^ 2 - 1) / ((D.q ^ 2 - 1).gcd (D.q + 1)) = D.q - 1
  have hq : 1 < D.q := D.one_lt_q
  have hsq : D.q ^ 2 - 1 = (D.q - 1) * (D.q + 1) := by
    zify [Nat.le_of_lt hq, show 1 ≤ D.q ^ 2 by nlinarith]; ring
  rw [hsq, Nat.gcd_eq_right (dvd_mul_left _ _), Nat.mul_div_cancel _ (by omega)]

lemma gen_ne_zero (D : FieldData) : D.gen ≠ 0 := by
  intro h
  have ho := orderOf_gen D
  rw [h, orderOf_zero] at ho
  have := D.one_lt_q
  omega

def uGen (D : FieldData) : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)

lemma orderOf_uGen (D : FieldData) : orderOf (uGen D) = D.q - 1 := by
  rw [← orderOf_injective (Units.coeHom D.Fq) Units.val_injective (uGen D)]
  exact orderOf_gen D

lemma exists_pow_gen (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : ∃ n : ℕ, D.gen ^ n = x := by
  let u := uGen D
  let φ : Fin (D.q - 1) → D.Fqˣ := fun k => u ^ k.val
  have hinj : Function.Injective φ := by
    intro i j hij
    have heq : u ^ i.val = u ^ j.val := hij
    rw [pow_eq_pow_iff_modEq, orderOf_uGen] at heq
    change i.val % (D.q - 1) = j.val % (D.q - 1) at heq
    ext
    rwa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at heq
  have hcard : Fintype.card (Fin (D.q - 1)) = Fintype.card D.Fqˣ := by
    rw [Fintype.card_fin, Fintype.card_units, card_Fq]
  have hbij := (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩
  obtain ⟨k, hk⟩ := hbij.2 (Units.mk0 x hx)
  exact ⟨k.val, by simpa [φ, u, uGen] using congrArg Units.val hk⟩

lemma gen_pow_dlog (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : D.gen ^ D.dlog x = x := by
  unfold dlog
  rw [dif_pos (exists_pow_gen D hx)]
  exact Nat.find_spec (exists_pow_gen D hx)

lemma dlogLab_injective (D : FieldData) :
    Function.Injective (fun x : D.Fqˣ => D.dlogLab (x : D.Fq)) := by
  intro x y hxy
  have hmod : D.dlog (x : D.Fq) ≡ D.dlog (y : D.Fq) [MOD (D.q - 1)] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hxy
  rw [← orderOf_uGen D, ← pow_eq_pow_iff_modEq] at hmod
  have hval := congrArg Units.val hmod
  change D.gen ^ D.dlog (x : D.Fq) = D.gen ^ D.dlog (y : D.Fq) at hval
  rw [gen_pow_dlog D x.ne_zero, gen_pow_dlog D y.ne_zero] at hval
  exact Units.val_injective hval

lemma bInEmb_injective (D : FieldData) : Function.Injective (bInEmb D) := by
  rintro ⟨a₁, d₁, b₁⟩ ⟨a₂, d₂, b₂⟩ h
  simp only [bInEmb, Prod.mk.injEq, Option.some.injEq] at h
  have ha := dlogLab_injective D h.1.1
  have hd := dlogLab_injective D h.1.2
  subst ha hd
  simp only [h.2]

lemma tagCode_xEmb_injective (D : FieldData) :
    Function.Injective (fun c : Option D.Lab => D.tagCode (D.xEmb c)) := by
  have hq : 2 ≤ D.q := D.one_lt_q
  have hqsq : 2 < D.q ^ 2 := by nlinarith
  have hlabW_pos : 0 < D.labW := by
    unfold labW
    exact Nat.clog_pos (by norm_num) (by omega)
  have hlt2pow : D.q - 1 < 2 ^ D.labW := by
    have hpow : D.q ^ 2 ≤ 2 ^ D.labW := Nat.le_pow_clog (by norm_num) _
    have : D.q < D.q ^ 2 := by nlinarith
    omega
  have hr2 : 2 ≤ D.r + 1 := Nat.succ_le_succ D.hr
  have hmul : 2 * D.labW ≤ (D.r + 1) * D.labW := Nat.mul_le_mul_right _ hr2
  have hposW : 0 < (D.r + 1) * D.labW := lt_of_lt_of_le (by omega) hmul
  intro c₁ c₂ h
  cases c₁ with
  | none =>
    cases c₂ with
    | none => rfl
    | some d₂ =>
      have h0 := congr_fun h ⟨0, hposW⟩
      simp [tagCode, xEmb, packNat, Nat.zero_div, Nat.zero_mod] at h0
  | some d₁ =>
    cases c₂ with
    | none =>
      have h0 := congr_fun h ⟨0, hposW⟩
      simp [tagCode, xEmb, packNat, Nat.zero_div, Nat.zero_mod] at h0
    | some d₂ =>
      congr 1
      apply ZMod.val_injective
      apply Nat.eq_of_testBit_eq
      intro k
      by_cases hk : k < D.labW
      · have hidx : D.labW + k < (D.r + 1) * D.labW := by omega
        have hb := congr_fun h ⟨D.labW + k, hidx⟩
        have hdiv : (D.labW + k) / D.labW = 1 := by
          rw [Nat.add_div_left _ hlabW_pos, Nat.div_eq_of_lt hk, zero_add]
        have hmod : (D.labW + k) % D.labW = k := by
          rw [Nat.add_mod_left, Nat.mod_eq_of_lt hk]
        simpa [tagCode, xEmb, packNat, hdiv, hmod] using hb
      · have : NeZero (D.q - 1) := ⟨by omega⟩
        have hk1 : d₁.val < 2 ^ k := lt_of_lt_of_le (lt_trans (ZMod.val_lt d₁) hlt2pow)
          (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hk))
        have hk2 : d₂.val < 2 ^ k := lt_of_lt_of_le (lt_trans (ZMod.val_lt d₂) hlt2pow)
          (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hk))
        rw [Nat.testBit_lt_two_pow hk1, Nat.testBit_lt_two_pow hk2]

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
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    rw [hnorm_sq, hnorm_sq]
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

lemma frameMatRight_iso {X Y B : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Fintype B] [DecidableEq B]
    {M : Matrix Y X ℂ} (hM : M.conjTranspose * M = 1) :
    (frameMatRight (B := B) M).conjTranspose * frameMatRight (B := B) M = 1 := by
  ext i j
  simp only [frameMatRight, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  dsimp only
  by_cases hij : i.2 = j.2
  · have hsum : (∑ y : Y, ∑ b : B, star (if b = i.2 then M y i.1 else 0) *
        (if b = j.2 then M y j.1 else 0)) = ∑ y : Y, star (M y i.1) * M y j.1 := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_eq_single i.2]
      · simp [hij]
      · intro b _ hb; simp [hb]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [hsum]
    have hm := congrFun (congrFun hM i.1) j.1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
    rw [hm]
    simp [hij, Prod.ext_iff]
  · rw [Finset.sum_eq_zero]
    · simp [Prod.ext_iff, hij]
    · intro y _; rw [Finset.sum_eq_zero]; intro b _
      by_cases hb : b = i.2
      · subst hb; simp [hij]
      · simp [hb]

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
    intro a _ b _ hab; exact hιY hab
  have hfull : (∑ y ∈ Finset.univ.image ιY, star (M y (ιX x₁')) * M y (ιX x₂')) =
      ∑ y : Y, star (M y (ιX x₁')) * M y (ιX x₂') := by
    refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
    have hnot : ∀ y', ιY y' ≠ y := fun y' h => hy (Finset.mem_image.mpr ⟨y', Finset.mem_univ y', h⟩)
    rw [hinv x₁' y hnot, star_zero, zero_mul]
  rw [himg, hfull]
  have hm := congrFun (congrFun hM (ιX x₁')) (ιX x₂')
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
  rw [hm]
  simp [hιX.eq_iff]

lemma appendCode_injective {X Y : Type} {m n : ℕ} {cx : X → Qubits m} {cy : Y → Qubits n}
    (hx : Function.Injective cx) (hy : Function.Injective cy) :
    Function.Injective (appendCode cx cy) := by
  rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  have h1 : cx x₁ = cx x₂ := funext fun i => by
    have := congr_fun h (Fin.castAdd n i)
    simpa [appendCode, Fin.append_left] using this
  have h2 : cy y₁ = cy y₂ := funext fun j => by
    have := congr_fun h (Fin.natAdd m j)
    simpa [appendCode, Fin.append_right] using this
  exact Prod.ext (hx h1) (hy h2)

def bStage3 (D : FieldData) : Matrix (Option D.Lab) D.Fq ℂ :=
  phiFmult D * phiLog D * phiFplus D

def bStage12 (D : FieldData) :
    Matrix ((Option D.Lab × Option D.Lab) × Option D.Lab)
      ((Option D.Lab × Option D.Lab) × Option D.Lab) ℂ :=
  frameMatRight (B := Option D.Lab) (frameMatRight (B := Option D.Lab) (phiFmult D)) *
    frameMatRight (B := Option D.Lab) (frameMat (A := Option D.Lab) (phiFmult D))

def bStageMat (D : FieldData) :
    Matrix ((Option D.Lab × Option D.Lab) × Option D.Lab) ((Option D.Lab × Option D.Lab) × D.Fq) ℂ :=
  bStage12 D * frameMat (A := Option D.Lab × Option D.Lab) (bStage3 D)

lemma bStage12_apply (D : FieldData) (a' d' η' x y z : Option D.Lab) :
    bStage12 D ((a', d'), η') ((x, y), z) =
      if η' = z then phiFmult D a' x * phiFmult D d' y else 0 := by
  unfold bStage12
  rw [Matrix.mul_apply]
  by_cases hz : η' = z
  · subst hz
    rw [if_pos rfl, Finset.sum_eq_single ((x, d'), η')]
    · simp [frameMatRight, frameMat]
    · rintro ⟨⟨u, v⟩, w⟩ _ hne
      by_cases hw : η' = w
      · by_cases hv : d' = v
        · by_cases hu : u = x
          · exact absurd (by subst hw hv hu; rfl) hne
          · simp [frameMatRight, frameMat, hw, hv, hu]
        · simp [frameMatRight, hw, hv]
      · simp [frameMatRight, hw]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [if_neg hz, Finset.sum_eq_zero]
    rintro ⟨⟨u, v⟩, w⟩ _
    by_cases hw : η' = w
    · subst hw; simp [frameMatRight, hz]
    · simp [frameMatRight, hw]

lemma bStageMat_apply (D : FieldData) (a' d' η? : Option D.Lab) (a d : Option D.Lab) (b : D.Fq) :
    bStageMat D ((a', d'), η?) ((a, d), b) =
      phiFmult D a' a * phiFmult D d' d * bStage3 D η? b := by
  unfold bStageMat
  rw [Matrix.mul_apply, Finset.sum_eq_single ((a, d), η?)]
  · rw [bStage12_apply, if_pos rfl]
    simp [frameMat]
  · rintro ⟨⟨x, y⟩, z⟩ _ hne
    by_cases hxy : (x, y) = (a, d)
    · by_cases hz : η? = z
      · rcases Prod.mk.inj hxy with ⟨rfl, rfl⟩
        exact absurd (by subst hz; rfl) hne
      · rw [bStage12_apply, if_neg hz, zero_mul]
    · simp [frameMat, hxy]
  · intro hm; exact absurd (Finset.mem_univ _) hm

end GL2QFT_Thm613_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.FieldData GL2QFT_Thm613_Aux

theorem solution :
    GL2QFT.UniformlyImplementsOn (fun _ => True) (X := fun D => D.BElt) (Y := fun D => D.BOutLabel)
      (inW := fun D => (D.r + 1) * D.labW + (D.r + 1) * D.labW + (D.r + 1) * D.labW)
      (outW := fun D => 5 * D.labW)
      (fun D => D.bInCode) (fun D => D.bOutCode) (fun D => D.qftB) := by
  have h68 := GL2QFT.lemma_6_8
  have hFplus : UniformlyImplementsOn (fun _ => True) (fun D a => D.tagCode (.inl a))
      (fun D a => D.tagCode (.inl a)) phiFplus := h68.1
  have hFmult : UniformlyImplementsOn (fun _ => True) (fun D c => D.tagCode (D.xEmb c))
      (fun D c => D.tagCode (D.xEmb c)) phiFmult := h68.2.1
  have hLog : UniformlyImplementsOn (fun _ => True) (fun D a => D.tagCode (.inl a))
      (fun D c => D.tagCode (D.xEmb c)) phiLog := h68.2.2.2
  have h3_1 := uniformlyImplementsOn_seq hFplus hLog
    (fun D _ => norm_mulVec_le_of_iso _ (phi_isometries D).1.1)
  have h3_2 := uniformlyImplementsOn_seq h3_1 hFmult
    (fun D _ => norm_mulVec_le_of_iso _
      (isometry_mul (phi_isometries D).1.1 (phi_isometries D).2.2.2.1))
  have h3 : UniformlyImplementsOn (fun _ => True) (fun D a => D.tagCode (.inl a))
      (fun D c => D.tagCode (D.xEmb c)) (fun D => phiFmult D * phiLog D * phiFplus D) :=
    uniformlyImplementsOn_eq h3_2 fun D _ => by simp only [Matrix.mul_assoc]
  have h3_iso : ∀ D : FieldData, (phiFmult D * phiLog D * phiFplus D).conjTranspose *
      (phiFmult D * phiLog D * phiFplus D) = 1 := fun D => by
    have := isometry_mul (isometry_mul (phi_isometries D).1.1 (phi_isometries D).2.2.2.1)
      (phi_isometries D).2.1.1
    simpa only [Matrix.mul_assoc] using this
  have hfw := GL2QFT.Circuits.fieldWidths_poly
  have hw1 : ∃ f : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str,
      QAlgorithms.Complexity.PolyTimeComputable f ∧
      ∀ D : FieldData, True → f D.encData = QAlgorithms.Complexity.encNat ((D.r + 1) * D.labW) :=
    let ⟨f, hf, heq⟩ := hfw.2.1; ⟨f, hf, fun D _ => heq D⟩
  have hw2 : ∃ f : QAlgorithms.Complexity.Str → QAlgorithms.Complexity.Str,
      QAlgorithms.Complexity.PolyTimeComputable f ∧
      ∀ D : FieldData, True →
        f D.encData = QAlgorithms.Complexity.encNat ((D.r + 1) * D.labW + (D.r + 1) * D.labW) :=
    let ⟨f, hf, heq⟩ := hfw.2.2.1; ⟨f, hf, fun D _ => heq D⟩
  let tagPair : ∀ D : FieldData, Option D.Lab × Option D.Lab →
      QAlgorithms.Qubits ((D.r + 1) * D.labW + (D.r + 1) * D.labW) :=
    fun D => appendCode (fun c => D.tagCode (D.xEmb c)) (fun c => D.tagCode (D.xEmb c))
  have htagPair_inj : ∀ D : FieldData, True → Function.Injective (tagPair D) :=
    fun D _ => appendCode_injective (tagCode_xEmb_injective D) (tagCode_xEmb_injective D)
  have hstage_b := uniformlyImplementsOn_frame tagPair h3 htagPair_inj hw2
  have hstage_d_inner := uniformlyImplementsOn_frame (fun D c => D.tagCode (D.xEmb c)) hFmult
    (fun D _ => tagCode_xEmb_injective D) hw1
  have hstage_d := uniformlyImplementsOn_frame_right (fun D c => D.tagCode (D.xEmb c)) hstage_d_inner
    (fun D _ => tagCode_xEmb_injective D) hw2 hw1
  have hstage_a_inner := uniformlyImplementsOn_frame_right (fun D c => D.tagCode (D.xEmb c)) hFmult
    (fun D _ => tagCode_xEmb_injective D) hw1 hw1
  have hstage_a := uniformlyImplementsOn_frame_right (fun D c => D.tagCode (D.xEmb c)) hstage_a_inner
    (fun D _ => tagCode_xEmb_injective D) hw2 hw1
  have hbd := uniformlyImplementsOn_seq hstage_b hstage_d
    (fun D _ => norm_mulVec_le_of_iso _ (frameMat_iso (h3_iso D)))
  have hbd_iso : ∀ D : FieldData,
      (frameMatRight (B := Option D.Lab) (frameMat (A := Option D.Lab) (phiFmult D)) *
        frameMat (A := Option D.Lab × Option D.Lab) (phiFmult D * phiLog D * phiFplus D)).conjTranspose *
      (frameMatRight (B := Option D.Lab) (frameMat (A := Option D.Lab) (phiFmult D)) *
        frameMat (A := Option D.Lab × Option D.Lab) (phiFmult D * phiLog D * phiFplus D)) = 1 :=
    fun D => isometry_mul (frameMat_iso (h3_iso D))
      (frameMatRight_iso (frameMat_iso (phi_isometries D).2.1.1))
  have hbda := uniformlyImplementsOn_seq hbd hstage_a
    (fun D _ => norm_mulVec_le_of_iso _ (hbd_iso D))
  have hbda_assoc : UniformlyImplementsOn (fun _ => True)
      (fun D => appendCode (tagPair D) (fun a => D.tagCode (.inl a)))
      (fun D => appendCode (tagPair D) (fun c => D.tagCode (D.xEmb c)))
      (fun D => bStageMat D) :=
    uniformlyImplementsOn_eq hbda fun D _ => by
      simp only [bStageMat, bStage12, bStage3, Matrix.mul_assoc]
  have hinv_sub : ∀ (D : FieldData) (x' : D.BElt) (y : (Option D.Lab × Option D.Lab) × Option D.Lab),
      (∀ y' : D.Lab × D.Lab × Option D.Lab, bMidInj D y' ≠ y) →
      bStageMat D y (bInEmb D x') = 0 := by
    intro D x' y hy
    rcases y with ⟨⟨a', d'⟩, η?⟩
    have hnone : a' = none ∨ d' = none := by
      cases a' with
      | none => exact Or.inl rfl
      | some a => cases d' with
        | none => exact Or.inr rfl
        | some d => exact absurd rfl (hy (a, d, η?))
    rw [bInEmb, bStageMat_apply]
    rcases hnone with rfl | rfl <;> simp [phiFmult]
  have hbMidInj_inj : ∀ D : FieldData, Function.Injective (bMidInj D) := by
    rintro D ⟨a₁, d₁, η₁⟩ ⟨a₂, d₂, η₂⟩ h
    simp only [bMidInj, Prod.mk.injEq, Option.some.injEq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  have hsub := uniformlyImplementsOn_restrict bInEmb bMidInj hbda_assoc
    (fun D _ => bInEmb_injective D) (fun D _ => hbMidInj_inj D) (fun D _ => hinv_sub D)
  have hsub_iso : ∀ D : FieldData,
      (Matrix.submatrix (bStageMat D) (bMidInj D) (bInEmb D)).conjTranspose *
      (Matrix.submatrix (bStageMat D) (bMidInj D) (bInEmb D)) = 1 := fun D => by
    have h12_iso : (bStage12 D).conjTranspose * bStage12 D = 1 :=
      isometry_mul (frameMatRight_iso (frameMat_iso (phi_isometries D).2.1.1))
        (frameMatRight_iso (frameMatRight_iso (phi_isometries D).2.1.1))
    have hfull_iso : (bStageMat D).conjTranspose * bStageMat D = 1 :=
      isometry_mul (frameMat_iso (h3_iso D)) h12_iso
    exact submatrix_iso (bStageMat D) hfull_iso (bInEmb D) (bMidInj D) (bInEmb_injective D)
      (hbMidInj_inj D) (hinv_sub D)
  have hcomp := uniformlyImplementsOn_seq hsub perm_FB_out_uniform
    (fun D _ => norm_mulVec_le_of_iso _ (hsub_iso D))
  exact uniformlyImplementsOn_eq hcomp fun D _ => by
    unfold bStageMat bStage12 bStage3
    exact (qftB_algebraic_factorization D).symm
