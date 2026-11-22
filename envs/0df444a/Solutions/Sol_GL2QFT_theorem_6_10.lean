-- Prove2me | solution 1 for GL2QFT.theorem_6_10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:30:16.222302+00:00
-- url     : https://prove2.me/submissions/1281da00-fc79-49ad-a73b-44371e88cdfd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GL2QFT_Uniform
import Definitions.Def_GL2QFT_Circuits_Combinators
import Theorems.Thm_GL2QFT_lemma_6_8
import Theorems.Thm_GL2QFT_Circuits_phi_isometries
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_seq
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_eq
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_controlled
import Theorems.Thm_GL2QFT_Circuits_uniformlyImplementsOn_restrict
import Theorems.Thm_GL2QFT_Circuits_gamma_circuit_identity
import Theorems.Thm_GL2QFT_Circuits_gamma_mark_phase_and_unmark

open Classical
noncomputable section

namespace GL2QFT_Thm610_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.FieldData QAlgorithms

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

end GL2QFT_Thm610_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.FieldData GL2QFT_Thm610_Aux

theorem solution :
    GL2QFT.UniformlyImplementsOn (fun _ => True)
      (X := fun D => Option D.Lab) (Y := fun D => Option D.Lab)
      (inW := fun D => (D.r + 1) * D.labW) (outW := fun D => (D.r + 1) * D.labW)
      (fun D c => D.tagCode (D.xEmb c)) (fun D c => D.tagCode (D.xEmb c))
      (fun D => Matrix.diagonal fun c =>
        match c with
        | none => 1
        | some α => if α = 0 then -1 else D.gauss α * isqrt D.q) := by
  have h68 := GL2QFT.lemma_6_8
  have hFplus : UniformlyImplementsOn (fun _ => True) (fun D a => D.tagCode (.inl a))
      (fun D a => D.tagCode (.inl a)) phiFplus := h68.1
  have hFmult : UniformlyImplementsOn (fun _ => True) (fun D c => D.tagCode (D.xEmb c))
      (fun D c => D.tagCode (D.xEmb c)) phiFmult := h68.2.1
  have hExp : UniformlyImplementsOn (fun _ => True) (fun D c => D.tagCode (D.xEmb c))
      (fun D a => D.tagCode (.inl a)) phiExp := h68.2.2.1
  have hLog : UniformlyImplementsOn (fun _ => True) (fun D a => D.tagCode (.inl a))
      (fun D c => D.tagCode (D.xEmb c)) phiLog := h68.2.2.2
  have h12 := uniformlyImplementsOn_seq hFmult hExp
    (fun D _ => norm_mulVec_le_of_iso _ (phi_isometries D).2.1.1)
  have h123 := uniformlyImplementsOn_seq h12 hFplus
    (fun D _ => norm_mulVec_le_of_iso _
      (isometry_mul (phi_isometries D).2.1.1 (phi_isometries D).2.2.1.1))
  have h1234 := uniformlyImplementsOn_seq h123 hLog
    (fun D _ => norm_mulVec_le_of_iso _
      (isometry_mul (isometry_mul (phi_isometries D).2.1.1 (phi_isometries D).2.2.1.1)
        (phi_isometries D).1.1))
  have h12345_raw := uniformlyImplementsOn_seq h1234 hFmult
    (fun D _ => norm_mulVec_le_of_iso _
      (isometry_mul (isometry_mul (isometry_mul (phi_isometries D).2.1.1 (phi_isometries D).2.2.1.1)
        (phi_isometries D).1.1) (phi_isometries D).2.2.2.1))
  have h12345 : UniformlyImplementsOn (fun _ => True) (fun D c => D.tagCode (D.xEmb c))
      (fun D c => D.tagCode (D.xEmb c))
      (fun D => phiFmult D * phiLog D * phiFplus D * phiExp D * phiFmult D) :=
    uniformlyImplementsOn_eq h12345_raw fun D _ => by
      simp only [Matrix.mul_assoc]
  have hctrl := uniformlyImplementsOn_controlled h12345
  let ι : ∀ D : FieldData, Option D.Lab → Bool × Option D.Lab := fun D c => (isNontrivLab c, c)
  have hrestr := uniformlyImplementsOn_restrict ι ι hctrl
    (fun _ _ _ _ h => congrArg Prod.snd h)
    (fun _ _ _ _ h => congrArg Prod.snd h)
    (fun D _ x' y hy => by
      rcases y with ⟨b', c'⟩
      have hne : b' ≠ isNontrivLab c' := fun heq => hy c' (Prod.ext heq.symm rfl)
      dsimp only [ι]
      simp only [ctrlMat, Matrix.of_apply]
      split_ifs with hb hnt
      · have hx' : ∃ α : D.Lab, α ≠ 0 ∧ x' = some α := by
          cases x' with
          | none => simp [isNontrivLab] at hnt
          | some α => exact ⟨α, by simpa [isNontrivLab] using hnt, rfl⟩
        rcases hx' with ⟨α, hα, rfl⟩
        rw [gamma_circuit_identity D α hα c']
        split_ifs with hc'
        · exfalso; apply hne; subst hc'; rw [← hb]
        · rfl
      · simp only [Matrix.one_apply]
        split_ifs with hc'
        · exfalso; apply hne; subst hc'; exact hb
        · rfl
      · rfl)
  let midDiag : ∀ D : FieldData, Matrix (Option D.Lab) (Option D.Lab) ℂ := fun D =>
    Matrix.diagonal fun c => match c with
      | none => 1
      | some α => if α = 0 then 1 else D.gauss α * isqrt D.q
  have hmid : UniformlyImplementsOn (fun _ => True)
      (fun D c => gammaTaggedCode D c) (fun D c => gammaTaggedCode D c) midDiag :=
    uniformlyImplementsOn_eq hrestr fun D _ => by
      ext out inp
      simp only [Matrix.submatrix_apply, ι, ctrlMat, Matrix.of_apply, midDiag, Matrix.diagonal_apply]
      cases inp with
      | none =>
        by_cases h : out = none <;> simp [isNontrivLab, Matrix.one_apply, h]
      | some α =>
        by_cases hα : α = 0
        · subst hα
          by_cases h : out = some 0 <;> simp [isNontrivLab, Matrix.one_apply, h]
        · have hnt : isNontrivLab (some α) = true := by simp [isNontrivLab, hα]
          by_cases hout : out = some α
          · subst hout
            simp [hnt, hα, gamma_circuit_identity D α hα (some α)]
          · simp only [hnt, hout, ↓reduceIte]
            split_ifs with hb
            · rw [gamma_circuit_identity D α hα out, if_neg hout]
            · rfl
  have hmid_iso : ∀ D : FieldData, (midDiag D).conjTranspose * midDiag D = 1 := by
    intro D
    have hΦ5 : (phiFmult D * phiLog D * phiFplus D * phiExp D * phiFmult D).conjTranspose *
        (phiFmult D * phiLog D * phiFplus D * phiExp D * phiFmult D) = 1 := by
      have hi := isometry_mul (isometry_mul (isometry_mul (isometry_mul
        (phi_isometries D).2.1.1 (phi_isometries D).2.2.1.1) (phi_isometries D).1.1)
        (phi_isometries D).2.2.2.1) (phi_isometries D).2.1.1
      simpa only [Matrix.mul_assoc] using hi
    ext i j
    simp only [midDiag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      cases i with
      | none => simp
      | some α =>
        by_cases hα : α = 0
        · simp [hα]
        · have hentry := congrFun (congrFun hΦ5 (some α)) (some α)
          rw [Matrix.mul_apply, Matrix.one_apply, if_pos rfl] at hentry
          simp only [Matrix.conjTranspose_apply] at hentry
          have hcollapse : (∑ x : Option D.Lab,
              star ((phiFmult D * phiLog D * phiFplus D * phiExp D * phiFmult D) x (some α)) *
              (phiFmult D * phiLog D * phiFplus D * phiExp D * phiFmult D) x (some α)) =
              star (D.gauss α * isqrt D.q) * (D.gauss α * isqrt D.q) := by
            rw [Finset.sum_eq_single (some α)]
            · rw [gamma_circuit_identity D α hα (some α), if_pos rfl]
            · intro c _ hc
              rw [gamma_circuit_identity D α hα c, if_neg hc]
              simp
            · intro hmem; exact absurd (Finset.mem_univ _) hmem
          rw [hcollapse] at hentry
          simpa [hα] using hentry
    · rw [Finset.sum_eq_zero]
      · simp [hij]
      · intro k _
        by_cases hki : k = i
        · subst hki; simp [hij]
        · simp [hki]
  have hmark := gamma_mark_phase_and_unmark.1
  have hunmark := gamma_mark_phase_and_unmark.2
  have hmark_iso : ∀ D : FieldData,
      (Matrix.diagonal fun c : Option D.Lab =>
        match c with | none => (1 : ℂ) | some α => if α = 0 then -1 else 1).conjTranspose *
      (Matrix.diagonal fun c : Option D.Lab =>
        match c with | none => (1 : ℂ) | some α => if α = 0 then -1 else 1) = 1 := by
    intro D; ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single i]
      · cases i with
        | none => simp
        | some α => by_cases hα : α = 0 <;> simp [hα]
      · intro k _ hk; simp [hk]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · rw [Finset.sum_eq_zero]
      · simp [hij]
      · intro k _
        by_cases hki : k = i
        · subst hki; simp [hij]
        · simp [hki]
  have hstep12 := uniformlyImplementsOn_seq hmark hmid
    (fun D _ => norm_mulVec_le_of_iso _ (hmark_iso D))
  have hstep123 := uniformlyImplementsOn_seq hstep12 hunmark
    (fun D _ => norm_mulVec_le_of_iso _ (isometry_mul (hmark_iso D) (hmid_iso D)))
  refine uniformlyImplementsOn_eq hstep123 fun D _ => ?_
  ext i j
  simp only [midDiag, Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · cases i with
      | none => simp
      | some α => by_cases hα : α = 0 <;> simp [hα]
    · intro k _ hk; simp [hk]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro k _; by_cases h1 : i = k
      · subst h1; simp [hij]
      · simp [h1]
