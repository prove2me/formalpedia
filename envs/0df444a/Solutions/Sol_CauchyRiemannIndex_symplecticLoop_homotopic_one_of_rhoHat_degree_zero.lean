-- Prove2me | solution 1 for CauchyRiemannIndex.symplecticLoop_homotopic_one_of_rhoHat_degree_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T16:54:21.709849+00:00
-- url     : https://prove2.me/submissions/89314c19-eeec-4b7b-ac12-a06efd953c6a

import Theorems.Thm_CauchyRiemannIndex_nonzeroLoop_homotopic_const_of_three_le_card
import Theorems.Thm_CauchyRiemannIndex_sp2Loop_vector_homotopic_of_rhoHat_degree_zero
import Theorems.Thm_CauchyRiemannIndex_exists_symplectic_transport
import Theorems.Thm_CauchyRiemannIndex_homotopy_lift_of_local_transport
import Theorems.Thm_CauchyRiemannIndex_symplecticLoop_fixing_vector_homotopic_diamond
import Theorems.Thm_CauchyRiemannIndex_rhoHat_increment_eq_of_symplectic_homotopy
import Theorems.Thm_CauchyRiemannIndex_diamond_isSymplectic
import Theorems.Thm_ConleyZehnder_rhoHat_diamond
import Theorems.Thm_ConleyZehnder_rhoHat_path_continuous
import Theorems.Thm_ConleyZehnder_argLift_exists_increment_unique
import Mathlib.Topology.Homotopy.Path

open Matrix CauchyRiemannIndex

namespace CRL

variable {n : ℕ}

/-- The symplectic group as a subtype. -/
abbrev Sp (n : ℕ) := ↥(Matrix.symplecticGroup (Fin n) ℝ)

/-- A based homotopy of symplectic loops from `φ` to `ψ`. -/
def RawHom (φ ψ : C(unitInterval, Mat n)) : Prop :=
  ∃ Φ : C(unitInterval × unitInterval, Mat n), (∀ t, Φ (0, t) = φ t) ∧ (∀ t, Φ (1, t) = ψ t) ∧
    (∀ s t, IsSymplectic (Φ (s, t))) ∧ (∀ s, Φ (s, 0) = 1) ∧ ∀ s, Φ (s, 1) = 1

/-- A symplectic loop based at `1`, as a path in `Sp n`. -/
def toPath (φ : C(unitInterval, Mat n)) (hs : ∀ t, IsSymplectic (φ t)) (h0 : φ 0 = 1)
    (h1 : φ 1 = 1) : Path (1 : Sp n) 1 where
  toFun t := ⟨φ t, hs t⟩
  continuous_toFun := φ.continuous.subtype_mk _
  source' := Subtype.ext h0
  target' := Subtype.ext h1

lemma RawHom.left {φ ψ : C(unitInterval, Mat n)} (h : RawHom φ ψ) :
    (∀ t, IsSymplectic (φ t)) ∧ φ 0 = 1 ∧ φ 1 = 1 := by
  obtain ⟨Φ, h0, -, hs, hb0, hb1⟩ := h
  exact ⟨fun t => h0 t ▸ hs 0 t, (h0 0).symm.trans (hb0 0), (h0 1).symm.trans (hb1 0)⟩

lemma RawHom.right {φ ψ : C(unitInterval, Mat n)} (h : RawHom φ ψ) :
    (∀ t, IsSymplectic (ψ t)) ∧ ψ 0 = 1 ∧ ψ 1 = 1 := by
  obtain ⟨Φ, -, h1, hs, hb0, hb1⟩ := h
  exact ⟨fun t => h1 t ▸ hs 1 t, (h1 0).symm.trans (hb0 1), (h1 1).symm.trans (hb1 1)⟩

lemma homotopic_of_rawHom {φ ψ : C(unitInterval, Mat n)} (h : RawHom φ ψ) :
    (toPath φ h.left.1 h.left.2.1 h.left.2.2).Homotopic
      (toPath ψ h.right.1 h.right.2.1 h.right.2.2) := by
  obtain ⟨Φ, h0, h1, hs, hb0, hb1⟩ := h
  refine ⟨{ toFun := fun p => ⟨Φ p, hs p.1 p.2⟩
            continuous_toFun := Φ.continuous.subtype_mk _
            map_zero_left := fun t => Subtype.ext (h0 t)
            map_one_left := fun t => Subtype.ext (h1 t)
            prop' := ?_ }⟩
  intro s t ht
  rcases ht with rfl | rfl
  · exact Subtype.ext ((hb0 s).trans ((h0 0).symm.trans (hb0 0)).symm)
  · exact Subtype.ext ((hb1 s).trans ((h0 1).symm.trans (hb1 0)).symm)

lemma rawHom_of_homotopic {φ ψ : C(unitInterval, Mat n)} {hφ hφ0 hφ1 hψ hψ0 hψ1}
    (h : (toPath φ hφ hφ0 hφ1).Homotopic (toPath ψ hψ hψ0 hψ1)) : RawHom φ ψ := by
  obtain ⟨F⟩ := h
  refine ⟨⟨fun p => (F p : Mat n), continuous_subtype_val.comp F.continuous⟩, fun t => ?_,
    fun t => ?_, fun s t => (F (s, t)).2, fun s => ?_, fun s => ?_⟩
  · simp only [ContinuousMap.coe_mk, ContinuousMap.HomotopyWith.apply_zero]; rfl
  · simp only [ContinuousMap.coe_mk, ContinuousMap.HomotopyWith.apply_one]; rfl
  · simp only [ContinuousMap.coe_mk, Path.Homotopy.source]; rfl
  · simp only [ContinuousMap.coe_mk, Path.Homotopy.target]; rfl

lemma RawHom.trans {φ ψ χ : C(unitInterval, Mat n)} (h₁ : RawHom φ ψ) (h₂ : RawHom ψ χ) :
    RawHom φ χ :=
  rawHom_of_homotopic ((homotopic_of_rawHom h₁).trans (homotopic_of_rawHom h₂))

lemma mulVec_ne_zero_of_symplectic {A : Mat n} (hA : IsSymplectic A)
    {v : Fin n ⊕ Fin n → ℝ} (hv : v ≠ 0) : A *ᵥ v ≠ 0 := by
  intro h; apply hv
  have hd := SymplecticGroup.symplectic_det hA
  calc v = (A⁻¹ * A) *ᵥ v := by rw [Matrix.nonsing_inv_mul _ hd, one_mulVec]
    _ = A⁻¹ *ᵥ (A *ᵥ v) := (mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [h, mulVec_zero]

lemma complexLinearDet_one : complexLinearDet (1 : Mat n) = 1 := by
  have hC : complexLinearPart (1 : Mat n) = 1 := by
    simp only [complexLinearPart, mul_one, J₀, Matrix.J_squared, sub_neg_eq_add]
    rw [← two_smul ℝ (1 : Mat n), smul_smul]; norm_num
  have h11 : (1 : Mat n).toBlocks₁₁ = 1 := by
    ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  have h21 : (1 : Mat n).toBlocks₂₁ = 0 := by
    ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply]
  simp [complexLinearDet, hC, h11, h21]

lemma rhoHat_one : rhoHat (1 : Mat n) = 1 := by
  simp [rhoHat, complexLinearDet_one]

lemma diamond_one_one : ConleyZehnder.diamond (1 : Mat n) (1 : Mat 1) = 1 := by
  unfold ConleyZehnder.diamond
  rw [Matrix.fromBlocks_one, Matrix.reindex_apply]
  exact Matrix.submatrix_one_equiv _

lemma continuous_diamond_one :
    Continuous (fun A : Mat n => ConleyZehnder.diamond A (1 : Mat 1)) := by
  unfold ConleyZehnder.diamond
  exact (continuous_id.matrix_fromBlocks continuous_const continuous_const
    continuous_const).matrix_reindex _ _

lemma rhoHat_diamond_one (A : Mat n) :
    rhoHat (ConleyZehnder.diamond A (1 : Mat 1)) = rhoHat A := by
  have := (ConleyZehnder.rhoHat_diamond A (1 : Mat 1)).2
  rw [show ConleyZehnder.rhoHat (1 : Mat 1) = 1 from rhoHat_one, mul_one] at this
  exact this

lemma exists_argLift (φ : C(unitInterval, Mat n)) (hs : ∀ t, IsSymplectic (φ t)) :
    ∃ θ, IsArgLift (fun t => rhoHat (φ t)) θ := by
  obtain ⟨hc, h1⟩ := ConleyZehnder.rhoHat_path_continuous φ hs
  exact (ConleyZehnder.argLift_exists_increment_unique hc h1).1

/-- The vector input of the induction step. -/
lemma exists_vector_homotopy (n : ℕ) (φ : C(unitInterval, Mat (n + 1)))
    (hs : ∀ t, IsSymplectic (φ t)) (h0 : φ 0 = 1) (h1 : φ 1 = 1) (θ : unitInterval → ℝ)
    (hθ : IsArgLift (fun t => rhoHat (φ t)) θ) (hθ1 : θ 1 = θ 0) :
    ∃ H : C(unitInterval × unitInterval, Fin (n + 1) ⊕ Fin (n + 1) → ℝ),
      (∀ t, H (0, t) = φ t *ᵥ Pi.single (Sum.inl (Fin.last n)) 1) ∧
      (∀ t, H (1, t) = Pi.single (Sum.inl (Fin.last n)) 1) ∧ (∀ p, H p ≠ 0) ∧
      (∀ s, H (s, 0) = Pi.single (Sum.inl (Fin.last n)) 1) ∧
      ∀ s, H (s, 1) = Pi.single (Sum.inl (Fin.last n)) 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact sp2Loop_vector_homotopic_of_rhoHat_degree_zero φ hs h0 h1 θ hθ hθ1
  · set e : Fin (n + 1) ⊕ Fin (n + 1) → ℝ := Pi.single (Sum.inl (Fin.last n)) 1
    have he : e ≠ 0 := fun h => by simpa [e] using congrFun h (Sum.inl (Fin.last n))
    let v : C(unitInterval, Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :=
      ⟨fun t => φ t *ᵥ e, φ.continuous.matrix_mulVec continuous_const⟩
    have hcard : 3 ≤ Fintype.card (Fin (n + 1) ⊕ Fin (n + 1)) := by
      simp only [Fintype.card_sum, Fintype.card_fin]; omega
    obtain ⟨H, hH0, hH1, hHne, hHb0, hHb1⟩ := nonzeroLoop_homotopic_const_of_three_le_card hcard e
      v (fun t => mulVec_ne_zero_of_symplectic (hs t) he)
      (by simp [v, h0]) (by simp [v, h1])
    exact ⟨H, hH0, hH1, hHne, hHb0, hHb1⟩

theorem main : ∀ (n : ℕ) (φ : C(unitInterval, Mat n)) (hs : ∀ t, IsSymplectic (φ t))
    (h0 : φ 0 = 1) (h1 : φ 1 = 1) (θ : unitInterval → ℝ)
    (hθ : IsArgLift (fun t => rhoHat (φ t)) θ) (hθ1 : θ 1 = θ 0),
    RawHom φ (ContinuousMap.const _ 1)
  | 0, φ, hs, h0, h1, θ, hθ, hθ1 => by
    refine ⟨ContinuousMap.const _ 1, fun t => Subsingleton.elim _ _, fun t => rfl,
      fun s t => (Matrix.symplecticGroup (Fin 0) ℝ).one_mem, fun s => rfl, fun s => rfl⟩
  | n + 1, φ, hs, h0, h1, θ, hθ, hθ1 => by
    set e : Fin (n + 1) ⊕ Fin (n + 1) → ℝ := Pi.single (Sum.inl (Fin.last n)) 1
    obtain ⟨H, hH0, hH1, hHne, hHb0, hHb1⟩ := exists_vector_homotopy n φ hs h0 h1 θ hθ hθ1
    obtain ⟨U, hU, hdiag, τ, hτc, hτ⟩ := exists_symplectic_transport (n + 1)
    obtain ⟨G, hG0, hGS, hGv, hGb⟩ := homotopy_lift_of_local_transport
      (Matrix.symplecticGroup (Fin (n + 1)) ℝ) U hU τ hτc (fun p hp => (hτ p hp).1)
      (fun p hp => (hτ p hp).2.1) (fun x hx => (hτ _ hx).2.2 rfl) H
      (fun p => hdiag _ (hHne p)) e φ hs (fun t => (hH0 t).symm)
    have hG0' : ∀ s, G (s, 0) = 1 := fun s =>
      (hGb 0 (fun s => (hHb0 s).trans (hHb0 0).symm) s).trans h0
    have hG1' : ∀ s, G (s, 1) = 1 := fun s =>
      (hGb 1 (fun s => (hHb1 s).trans (hHb1 0).symm) s).trans h1
    let B : C(unitInterval, Mat (n + 1)) := ⟨fun t => G (1, t), by fun_prop⟩
    have hBs : ∀ t, IsSymplectic (B t) := fun t => hGS _
    have hR1 : RawHom φ B := ⟨G, hG0, fun t => rfl, fun s t => hGS _, hG0', hG1'⟩
    obtain ⟨B', hB's, hB'0, hB'1, Φ₂, hΦ0, hΦ1, hΦs, hΦb0, hΦb1⟩ :=
      symplecticLoop_fixing_vector_homotopic_diamond n B hBs (hG0' 1) (hG1' 1)
        (fun t => (hGv (1, t)).trans (hH1 t))
    have hR2 : RawHom B ⟨fun t => ConleyZehnder.diamond (B' t) (1 : Mat 1),
        continuous_diamond_one.comp B'.continuous⟩ :=
      ⟨Φ₂, hΦ0, hΦ1, hΦs, hΦb0, hΦb1⟩
    -- the degree of `B'`
    obtain ⟨θB, hθB⟩ := exists_argLift B hBs
    obtain ⟨θ', hθ'⟩ := exists_argLift B' hB's
    have i1 := rhoHat_increment_eq_of_symplectic_homotopy G (fun p => hGS p)
      (fun s => (hG0' s).trans (hG0' 0).symm) (fun s => (hG1' s).trans (hG1' 0).symm) θ θB
      (by simpa only [hG0] using hθ) hθB
    have hθ'D : IsArgLift (fun t => rhoHat (Φ₂ (1, t))) θ' := by
      refine ⟨hθ'.1, fun t => ?_⟩
      show rhoHat (Φ₂ (1, t)) = _
      rw [hΦ1, rhoHat_diamond_one]; exact hθ'.2 t
    have i2 := rhoHat_increment_eq_of_symplectic_homotopy Φ₂ (fun p => hΦs p.1 p.2)
      (fun s => (hΦb0 s).trans (hΦb0 0).symm) (fun s => (hΦb1 s).trans (hΦb1 0).symm) θB θ'
      (by simpa only [hΦ0] using hθB) hθ'D
    obtain ⟨Φ₃, h30, h31, h3s, h3b0, h3b1⟩ :=
      main n B' hB's hB'0 hB'1 θ' hθ' (by linarith)
    have hR3 : RawHom ⟨fun t => ConleyZehnder.diamond (B' t) (1 : Mat 1),
        continuous_diamond_one.comp B'.continuous⟩ (ContinuousMap.const _ 1) := by
      refine ⟨⟨fun p => ConleyZehnder.diamond (Φ₃ p) (1 : Mat 1),
        continuous_diamond_one.comp Φ₃.continuous⟩, fun t => ?_, fun t => ?_,
        fun s t => diamond_isSymplectic _ _ (h3s s t)
          (Matrix.symplecticGroup (Fin 1) ℝ).one_mem, fun s => ?_, fun s => ?_⟩
      · simp [h30]
      · simp [h31, diamond_one_one]
      · simp [h3b0, diamond_one_one]
      · simp [h3b1, diamond_one_one]
    exact hR1.trans (hR2.trans hR3)

end CRL

theorem solution (n : ℕ)
    (φ : C(unitInterval, Mat n)) (hs : ∀ t, IsSymplectic (φ t)) (h0 : φ 0 = 1)
    (h1 : φ 1 = 1) (θ : unitInterval → ℝ) (hθ : IsArgLift (fun t => rhoHat (φ t)) θ)
    (hθ1 : θ 1 = θ 0) :
    ∃ Φ : C(unitInterval × unitInterval, Mat n), (∀ t, Φ (0, t) = φ t) ∧
      (∀ t, Φ (1, t) = 1) ∧ (∀ s t, IsSymplectic (Φ (s, t))) ∧ (∀ s, Φ (s, 0) = 1) ∧
      ∀ s, Φ (s, 1) = 1 :=
  CRL.main n φ hs h0 h1 θ hθ hθ1
