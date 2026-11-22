-- Prove2me | solution 1 for GL2QFT.theorem_6_34
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T06:54:09.498329+00:00
-- url     : https://prove2.me/submissions/0d3c0dbb-7cca-4b39-974a-977c555afb0c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GL2QFT_Uniform
import Definitions.Def_GL2QFT_AGamma
import Definitions.Def_GL2QFT_Circuits_Leaves
import Theorems.Thm_GL2QFT_Supplement_theorem_6_27
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_seq
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_eq
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_unpad_out
import Theorems.Thm_GL2QFT_Circuits_canonMbr_Rfix_valid
import Theorems.Thm_GL2QFT_Circuits_stage_Dgate_uniform
import Theorems.Thm_GL2QFT_Circuits_stage_FxDag_uniform
import Theorems.Thm_GL2QFT_Circuits_stage_Bgate_uniform
import Theorems.Thm_GL2QFT_Circuits_stage_Mbr_uniform
import Theorems.Thm_GL2QFT_Circuits_stage_Rfix_uniform
import Theorems.Thm_GL2QFT_Circuits_stage_Rexc_uniform

open Classical
noncomputable section

namespace GL2QFT_Thm634_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.FieldData GL2QFT.Supplement GL2QFT.Supplement.AGammaGates QAlgorithms

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

lemma subMat_iso {A X Y : Type} [Fintype A] [DecidableEq A] [Fintype X] [DecidableEq X] [Fintype Y]
    (Φ : A → Matrix Y X ℂ) (hΦ : ∀ a, (Φ a).conjTranspose * Φ a = 1) :
    (subMat Φ).conjTranspose * subMat Φ = 1 := by
  ext i j
  simp only [subMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  dsimp only
  by_cases hij : i.1 = j.1
  · rw [Finset.sum_eq_single i.1]
    · simp only [↓reduceIte, hij]
      have hm := congrFun (congrFun (hΦ i.1) i.2) j.2
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
      rw [← hij, hm]
      simp [hij, Prod.ext_iff]
    · intro a _ ha
      rw [Finset.sum_eq_zero]
      intro y _; simp [ha]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [Finset.sum_eq_zero]
    · simp [Prod.ext_iff, hij]
    · intro a _; rw [Finset.sum_eq_zero]; intro y _
      by_cases ha : a = i.1
      · subst ha; simp [hij]
      · simp [ha]

lemma frameMat_iso {A X Y : Type} [Fintype A] [DecidableEq A] [Fintype X] [DecidableEq X] [Fintype Y]
    {M : Matrix Y X ℂ} (hM : M.conjTranspose * M = 1) :
    (frameMat (A := A) M).conjTranspose * frameMat (A := A) M = 1 :=
  subMat_iso (fun _ => M) fun _ => hM

def M4 (D : FieldData) : Matrix (BranchPair D) (D.Lab × BranchSrc D) ℂ :=
  Matrix.of fun out inp =>
    if h : out.1 = inp.1 then canonMbrCore D inp.1 (cast (congrArg (BranchOut D) h) out.2) inp.2 else 0

def M5 (D : FieldData) : Matrix (D.Lab × (D.Irr ⊕ D.Irr)) (BranchPair D) ℂ :=
  Matrix.of fun out inp =>
    if h : out.1 = inp.1 then canonRfix D out.1 out.2 (cast (congrArg (BranchOut D) h.symm) inp.2) else 0

lemma M4_iso (D : FieldData) (hq : 2 < D.q) : (M4 D).conjTranspose * M4 D = 1 := by
  ext x₁ x₂
  simp only [M4, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single x₁.1]
  · by_cases hγ : x₁.1 = x₂.1
    · obtain ⟨γ₁, a₁⟩ := x₁
      obtain ⟨γ₂, a₂⟩ := x₂
      dsimp only at hγ ⊢
      subst hγ
      have hm := congrFun (congrFun (canonMbr_Rfix_valid D hq γ₁).2.2.2.2.2.2.1 a₁) a₂
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
      simpa [Prod.ext_iff] using hm
    · rw [Finset.sum_eq_zero]
      · simp [Prod.ext_iff, hγ]
      · intro y _; simp [hγ]
  · intro γ _ hγ
    rw [Finset.sum_eq_zero]
    intro y _; simp [hγ]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma M5_iso (D : FieldData) (hq : 2 < D.q) : (M5 D).conjTranspose * M5 D = 1 := by
  ext i₁ i₂
  simp only [M5, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i₁.1]
  · by_cases hγ : i₁.1 = i₂.1
    · obtain ⟨γ₁, b₁⟩ := i₁
      obtain ⟨γ₂, b₂⟩ := i₂
      dsimp only at hγ ⊢
      subst hγ
      have hm := congrFun (congrFun (canonMbr_Rfix_valid D hq γ₁).2.2.2.2.2.2.2 b₁) b₂
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
      simpa using hm
    · rw [Finset.sum_eq_zero]
      · simp [Sigma.ext_iff, hγ]
      · intro o _; simp [hγ]
  · intro γ _ hγ
    rw [Finset.sum_eq_zero]
    intro o _; simp [hγ]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma prod6_eq (D : FieldData) (hq : 2 < D.q) :
    subMat (fun γ => Rexc D γ D.Irr) *
        (M5 D * (M4 D * (subMat (BgateSub D) * (frameMat (A := D.Lab) (FxDag D) * subMat (Dgate D))))) =
      Matrix.of fun (out : D.Lab × (D.Irr ⊕ D.Irr)) (inp : D.Lab × Option D.Lab) =>
        if out.1 = inp.1 then AGammaExt D inp.1 D.Irr out.2 inp.2 else 0 := by
  ext ⟨γ', o'⟩ ⟨γ, c⟩
  have h12 : ∀ p : D.Lab × D.Fq,
      (frameMat (A := D.Lab) (FxDag D) * subMat (Dgate D)) p (γ, c) =
        if p.1 = γ then (FxDag D * Dgate D γ) p.2 c else 0 := by
    intro ⟨γ₁, t⟩
    simp only [frameMat, subMat, Matrix.mul_apply, Matrix.of_apply]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single γ]
    · by_cases h : γ₁ = γ
      · subst h; simp
      · simp [h]
    · intro γ₀ _ hγ₀; rw [Finset.sum_eq_zero]; intro d _; simp [hγ₀]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have h123 : ∀ p : D.Lab × BranchSrc D,
      (subMat (BgateSub D) * (frameMat (A := D.Lab) (FxDag D) * subMat (Dgate D))) p (γ, c) =
        if p.1 = γ then (BgateSub D γ * (FxDag D * Dgate D γ)) p.2 c else 0 := by
    intro ⟨γ₁, br⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single γ]
    · have hterm : ∀ t : D.Fq,
          (subMat (BgateSub D)) (γ₁, br) (γ, t) *
            (frameMat (A := D.Lab) (FxDag D) * subMat (Dgate D)) (γ, t) (γ, c) =
            (subMat (BgateSub D)) (γ₁, br) (γ, t) * (FxDag D * Dgate D γ) t c := fun t => by
        rw [h12 (γ, t), if_pos rfl]
      simp_rw [hterm]
      by_cases h : γ₁ = γ
      · subst h; simp [subMat, Matrix.mul_apply]
      · simp [subMat, h]
    · intro γ₀ _ hγ₀
      rw [Finset.sum_eq_zero]; intro t _; rw [h12 (γ₀, t), if_neg hγ₀, mul_zero]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have h1234 : ∀ p : BranchPair D,
      (M4 D * (subMat (BgateSub D) * (frameMat (A := D.Lab) (FxDag D) * subMat (Dgate D)))) p (γ, c) =
        if h : p.1 = γ then
          (canonMbr D γ * Bgate D γ * (FxDag D * Dgate D γ)) (cast (congrArg (BranchOut D) h) p.2) c
        else 0 := by
    intro ⟨γ₁, bo⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single γ]
    · by_cases h : γ₁ = γ
      · subst h
        have hcore := (canonMbr_Rfix_valid D hq γ₁).2.2.1
        simp only [M4, Matrix.of_apply, h123, ↓reduceDIte, ↓reduceIte, cast_eq]
        have hprod : (canonMbrCore D γ₁ * (BgateSub D γ₁ * (FxDag D * Dgate D γ₁))) bo c =
            (canonMbr D γ₁ * Bgate D γ₁ * (FxDag D * Dgate D γ₁)) bo c := by
          rw [← Matrix.mul_assoc, ← hcore]
        simpa [Matrix.mul_apply] using hprod
      · simp [M4, h]
    · intro γ₀ _ hγ₀; rw [Finset.sum_eq_zero]; intro br _; rw [h123, if_neg hγ₀, mul_zero]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have h12345 : ∀ p : D.Lab × (D.Irr ⊕ D.Irr),
      (M5 D * (M4 D * (subMat (BgateSub D) * (frameMat (A := D.Lab) (FxDag D) * subMat (Dgate D))))) p (γ, c) =
        if p.1 = γ then (canonRfix D γ * (canonMbr D γ * Bgate D γ * (FxDag D * Dgate D γ))) p.2 c else 0 := by
    intro ⟨γ₁, u⟩
    rw [Matrix.mul_apply, Fintype.sum_sigma]
    rw [Finset.sum_eq_single γ]
    · by_cases h : γ₁ = γ
      · subst h
        simp only [M5, Matrix.of_apply, h1234, ↓reduceDIte, ↓reduceIte, cast_eq, Matrix.mul_apply]
      · simp [M5, h]
    · intro γ₀ _ hγ₀; rw [Finset.sum_eq_zero]; intro bo _; rw [h1234, dif_neg hγ₀, mul_zero]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single γ]
  · by_cases h : γ' = γ
    · subst h
      have hvalid := canonMbr_Rfix_valid D hq γ'
      have h627 := theorem_6_27 D hq γ' D.Irr (canonRfix D γ') hvalid.2.1 (canonMbr D γ') hvalid.1
      have hassoc : Rexc D γ' D.Irr * (canonRfix D γ' * (canonMbr D γ' * Bgate D γ' * (FxDag D * Dgate D γ'))) =
          AGammaExt D γ' D.Irr := by
        simpa only [Matrix.mul_assoc] using h627
      have helem := congrFun (congrFun hassoc o') c
      have hterm : ∀ u : D.Irr ⊕ D.Irr,
          (subMat (fun γ => Rexc D γ D.Irr)) (γ', o') (γ', u) *
            (M5 D * (M4 D * (subMat (BgateSub D) * (frameMat (A := D.Lab) (FxDag D) * subMat (Dgate D))))) (γ', u) (γ', c) =
            Rexc D γ' D.Irr o' u * (canonRfix D γ' * (canonMbr D γ' * Bgate D γ' * (FxDag D * Dgate D γ'))) u c := by
        intro u
        rw [h12345 (γ', u), if_pos rfl]
        simp [subMat]
      simp_rw [hterm]
      simpa only [Matrix.of_apply, ↓reduceIte, Matrix.mul_apply] using helem
    · rw [Finset.sum_eq_zero]
      · simp [h]
      · intro u _
        have h0 : (subMat (fun γ => Rexc D γ D.Irr)) (γ', o') (γ, u) = 0 := by
          simp [subMat, h]
        rw [h0, zero_mul]
  · intro γ₀ _ hγ₀; rw [Finset.sum_eq_zero]; intro u _; rw [h12345 (γ₀, u), if_neg hγ₀, mul_zero]
  · intro hm; exact absurd (Finset.mem_univ _) hm

end GL2QFT_Thm634_Aux

open Classical GL2QFT GL2QFT.FieldData GL2QFT.Circuits GL2QFT.Supplement.AGammaGates GL2QFT_Thm634_Aux

theorem solution :
    UniformlyImplementsOn (fun D => 2 < D.q) (X := fun D => D.Lab × Option D.Lab)
      (Y := fun D => D.Lab × D.Irr)
      (inW := fun D => 1 * D.labW + (D.r + 1) * D.labW) (outW := fun D => 4 * D.labW)
      (fun D => D.gammaInCode) (fun D => D.gammaIrrCode)
      (fun D => fun out inp => if out.1 = inp.1 then D.AGamma inp.1 out.2 inp.2 else 0) := by
  have h12 := uniformlyImplementsOn_seq stage_Dgate_uniform stage_FxDag_uniform fun D hq ψ =>
    norm_mulVec_le_of_iso _ (subMat_iso _ fun γ => (canonMbr_Rfix_valid D hq γ).2.2.2.1) ψ
  have h123 := uniformlyImplementsOn_seq h12 stage_Bgate_uniform fun D hq ψ =>
    norm_mulVec_le_of_iso _
      (isometry_mul
        (subMat_iso _ fun γ => (canonMbr_Rfix_valid D hq γ).2.2.2.1)
        (frameMat_iso (canonMbr_Rfix_valid D hq 0).2.2.2.2.1)) ψ
  have h1234 := uniformlyImplementsOn_seq h123 stage_Mbr_uniform fun D hq ψ =>
    norm_mulVec_le_of_iso _
      (isometry_mul
        (isometry_mul
          (subMat_iso _ fun γ => (canonMbr_Rfix_valid D hq γ).2.2.2.1)
          (frameMat_iso (canonMbr_Rfix_valid D hq 0).2.2.2.2.1))
        (subMat_iso _ fun γ => (canonMbr_Rfix_valid D hq γ).2.2.2.2.2.1)) ψ
  have h12345 := uniformlyImplementsOn_seq h1234 stage_Rfix_uniform fun D hq ψ =>
    norm_mulVec_le_of_iso _
      (isometry_mul
        (isometry_mul
          (isometry_mul
            (subMat_iso _ fun γ => (canonMbr_Rfix_valid D hq γ).2.2.2.1)
            (frameMat_iso (canonMbr_Rfix_valid D hq 0).2.2.2.2.1))
          (subMat_iso _ fun γ => (canonMbr_Rfix_valid D hq γ).2.2.2.2.2.1))
        (M4_iso D hq)) ψ
  have h123456 := uniformlyImplementsOn_seq h12345 stage_Rexc_uniform fun D hq ψ =>
    norm_mulVec_le_of_iso _
      (isometry_mul
        (isometry_mul
          (isometry_mul
            (isometry_mul
              (subMat_iso _ fun γ => (canonMbr_Rfix_valid D hq γ).2.2.2.1)
              (frameMat_iso (canonMbr_Rfix_valid D hq 0).2.2.2.2.1))
            (subMat_iso _ fun γ => (canonMbr_Rfix_valid D hq γ).2.2.2.2.2.1))
          (M4_iso D hq))
        (M5_iso D hq)) ψ
  have hAGext : UniformlyImplementsOn (fun D => 2 < D.q) (fun D => D.gammaInCode)
      (fun D => gammaExtCode D)
      (fun D => Matrix.of fun out inp => if out.1 = inp.1 then AGammaExt D inp.1 D.Irr out.2 inp.2 else 0) :=
    uniformlyImplementsOn_eq h123456 fun D hq => prod6_eq D hq
  have hunpad := uniformlyImplementsOn_unpad_out (fun D (p : D.Lab × D.Irr) => (p.1, Sum.inl p.2))
    hAGext
    (fun D _ p₁ p₂ h => by
      rcases p₁, p₂ with ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩
      simp only [Prod.mk.injEq, Sum.inl.injEq] at h
      simp [h])
    (fun D p => by rfl)
    (fun D _ z inp hz => by
      rcases z with ⟨γ', o⟩
      cases o with
      | inl μ => exact absurd rfl (hz (γ', μ))
      | inr u => simp [AGammaExt])
  exact uniformlyImplementsOn_eq hunpad fun D _ => by ext ⟨γ', μ⟩ ⟨γ, c⟩; simp [AGammaExt]
