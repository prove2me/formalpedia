-- Prove2me | solution 1 for GL2QFT.Circuits.stage_FxDag_uniform
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T06:53:46.570854+00:00
-- url     : https://prove2.me/submissions/0ed383bd-be1d-4691-9679-021f811dad62
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GL2QFT_Circuits_Leaves
import Theorems.Thm_GL2QFT_Circuits_lemma_6_8_Fmult
import Theorems.Thm_GL2QFT_Circuits_lemma_6_8_log_g
import Theorems.Thm_GL2QFT_Circuits_phi_isometries
import Theorems.Thm_GL2QFT_Circuits_fieldWidths_poly
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_adjoint
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_seq
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_frame
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_eq
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_mono

noncomputable section

open Classical
open GL2QFT GL2QFT.Circuits GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT_StageFxDag_Aux

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
  unfold FieldData.gen
  have hnorm := @FiniteField.algebraMap_norm_eq_pow D.Fq D.Fq2 _ _ _ _ D.h
  rw [hnorm, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_Fq2, card_Fq]
  have hq : 1 < D.q := D.one_lt_q
  have hsq : D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by
    zify [Nat.le_of_lt hq, show 1 ≤ D.q ^ 2 by nlinarith]
    ring
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
    zify [Nat.le_of_lt hq, show 1 ≤ D.q ^ 2 by nlinarith]
    ring
  rw [hsq, Nat.gcd_eq_right (dvd_mul_left _ _), Nat.mul_div_cancel _ (by omega)]

lemma gen_ne_zero (D : FieldData) : D.gen ≠ 0 := by
  intro h
  have ho := orderOf_gen D
  rw [h, orderOf_zero] at ho
  have := D.one_lt_q
  omega

def labEquivUnits (D : FieldData) : D.Lab ≃ D.Fqˣ := by
  let u : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)
  have hu : orderOf u = D.q - 1 := by
    rw [← orderOf_injective (Units.coeHom D.Fq) Units.val_injective u]
    exact orderOf_gen D
  let φ : D.Lab → D.Fqˣ := fun k => u ^ k.val
  have hinj : Function.Injective φ := by
    intro i j hij
    have hmod : i.val ≡ j.val [MOD orderOf u] := pow_eq_pow_iff_modEq.mp hij
    rw [hu] at hmod
    exact ZMod.val_injective _ (Nat.ModEq.eq_of_lt_of_lt hmod (ZMod.val_lt i) (ZMod.val_lt j))
  have hcard : Fintype.card D.Lab = Fintype.card D.Fqˣ := by
    rw [ZMod.card, Fintype.card_units, card_Fq]
  exact Equiv.ofBijective φ ((Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩)

lemma labEquivUnits_val (D : FieldData) (d : D.Lab) :
    ((labEquivUnits D d : D.Fqˣ) : D.Fq) = D.gen ^ d.val := by
  change (((Units.mk0 D.gen (gen_ne_zero D) : D.Fqˣ) ^ d.val : D.Fqˣ) : D.Fq) = D.gen ^ d.val
  rw [Units.val_pow_eq_pow_val]
  rfl

lemma existsUnique_pow_gen (D : FieldData) {t : D.Fq} (ht : t ≠ 0) :
    ∃! d : D.Lab, D.gen ^ d.val = t := by
  let e := labEquivUnits D
  let tu : D.Fqˣ := Units.mk0 t ht
  refine ⟨e.symm tu, ?_, ?_⟩
  · have h : ((e (e.symm tu) : D.Fqˣ) : D.Fq) = t := by
      rw [e.apply_symm_apply tu]
      rfl
    dsimp only
    rw [← labEquivUnits_val D (e.symm tu)]
    exact h
  · intro d hd
    apply e.injective
    rw [e.apply_symm_apply]
    apply Units.ext
    change ((labEquivUnits D d : D.Fqˣ) : D.Fq) = t
    rw [labEquivUnits_val]
    exact hd

lemma phiLog_conj_mul_phiFmult_conj (D : FieldData) :
    (phiLog D).conjTranspose * (phiFmult D).conjTranspose = FxDag D := by
  ext t c
  rw [Matrix.mul_apply, Fintype.sum_option]
  cases c with
  | none =>
      have h0 : (phiLog D).conjTranspose t none * (phiFmult D).conjTranspose none none =
          if t = 0 then 1 else 0 := by
        simp [Matrix.conjTranspose_apply, phiLog, phiFmult]
      have hs : ∀ d : D.Lab,
          (phiLog D).conjTranspose t (some d) * (phiFmult D).conjTranspose (some d) none = 0 := by
        intro d
        simp [Matrix.conjTranspose_apply, phiFmult]
      rw [h0, Finset.sum_eq_zero (fun d _ => hs d), add_zero]
      simp [FxDag]
  | some α =>
      have h0 : (phiLog D).conjTranspose t none * (phiFmult D).conjTranspose none (some α) = 0 := by
        simp [Matrix.conjTranspose_apply, phiFmult]
      rw [h0, zero_add]
      by_cases ht : t = 0
      · subst ht
        simp [Matrix.conjTranspose_apply, phiLog, FxDag]
      · obtain ⟨d₀, hd₀, hd₀_uniq⟩ := existsUnique_pow_gen D ht
        rw [Finset.sum_eq_single d₀]
        · have hisq : star (FieldData.isqrt ((D.q : ℝ) - 1)) = FieldData.isqrt ((D.q : ℝ) - 1) := by
            simp [FieldData.isqrt]
          simp [Matrix.conjTranspose_apply, phiLog, phiFmult, ht, hd₀, hisq, FxDag,
            RCLike.star_def]
        · intro d _ hd
          have hne : D.gen ^ d.val ≠ t := fun h => hd (hd₀_uniq d h)
          simp [Matrix.conjTranspose_apply, phiLog, hne]
        · intro hm
          exact absurd (Finset.mem_univ _) hm

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

lemma gammaLab_injective (D : FieldData) :
    Function.Injective (fun γ : D.Lab => packNat 1 D.labW ![γ.val]) := by
  have hq : 2 ≤ D.q := D.one_lt_q
  have hlt2pow : D.q - 1 < 2 ^ D.labW := by
    have hpow : D.q ^ 2 ≤ 2 ^ D.labW := Nat.le_pow_clog (by norm_num) _
    have : D.q < D.q ^ 2 := by nlinarith
    omega
  intro γ₁ γ₂ h
  apply ZMod.val_injective
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hlt : k < D.labW
  · have hidx : k < 1 * D.labW := by omega
    have hb := congr_fun h ⟨k, hidx⟩
    have hdiv : k / D.labW = 0 := Nat.div_eq_of_lt hlt
    have hmod : k % D.labW = k := Nat.mod_eq_of_lt hlt
    simpa [packNat, hdiv, hmod] using hb
  · have hb1 : γ₁.val < 2 ^ k := lt_of_lt_of_le (lt_trans (ZMod.val_lt γ₁) hlt2pow)
      (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hlt))
    have hb2 : γ₂.val < 2 ^ k := lt_of_lt_of_le (lt_trans (ZMod.val_lt γ₂) hlt2pow)
      (Nat.pow_le_pow_right (by norm_num) (le_of_not_gt hlt))
    rw [Nat.testBit_lt_two_pow hb1, Nat.testBit_lt_two_pow hb2]

end GL2QFT_StageFxDag_Aux

theorem solution :
    UniformlyImplementsOn (fun D => 2 < D.q) (fun D => D.gammaInCode) (fun D => gammaFqCode D)
      (fun D => frameMat (A := D.Lab) (FxDag D)) := by
  have hFmultAdj : UniformlyImplementsOn (fun _ => True)
      (fun D c => D.tagCode (D.xEmb c)) (fun D c => D.tagCode (D.xEmb c))
      (fun D => (phiFmult D).conjTranspose) :=
    uniformlyImplementsOn_adjoint lemma_6_8_Fmult (fun D _ => by convert (phi_isometries D).2.1)
  have hLogAdj : UniformlyImplementsOn (fun _ => True)
      (fun D c => D.tagCode (D.xEmb c)) (fun D a => D.tagCode (.inl a))
      (fun D => (phiLog D).conjTranspose) :=
    uniformlyImplementsOn_adjoint lemma_6_8_log_g (fun D _ => by convert (phi_isometries D).2.2.2)
  have hSeq := uniformlyImplementsOn_seq hFmultAdj hLogAdj fun D _ ψ =>
    GL2QFT_StageFxDag_Aux.norm_mulVec_le_of_iso ((phiFmult D).conjTranspose)
      (by convert (phi_isometries D).2.1.2; rw [Matrix.conjTranspose_conjTranspose]) ψ
  have hFxDag := uniformlyImplementsOn_eq hSeq fun D _ =>
    GL2QFT_StageFxDag_Aux.phiLog_conj_mul_phiFmult_conj D
  have hFramed := uniformlyImplementsOn_frame
    (fun D (γ : D.Lab) => packNat 1 D.labW ![γ.val]) hFxDag
    (fun D _ => GL2QFT_StageFxDag_Aux.gammaLab_injective D)
    (by
      obtain ⟨fw, hfw, hfeq⟩ := fieldWidths_poly.1
      exact ⟨fw, hfw, fun D _ => by simpa [one_mul] using hfeq D⟩)
  have hMono := uniformlyImplementsOn_mono (P' := fun D => 2 < D.q) hFramed (fun _ _ => trivial)
  convert hMono using 1 <;> rfl
