-- Prove2me | solution 1 for CauchyRiemannIndex.symplecticPath_family_of_czIndex_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T15:46:42.5522+00:00
-- url     : https://prove2.me/submissions/1c95aed5-4ae8-4a31-9741-253997a052a2

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_CauchyRiemannIndex_spStar_joinedIn_of_sign_det_eq
import Theorems.Thm_CauchyRiemannIndex_symplecticLoop_homotopic_one_of_rhoHat_degree_zero
import Theorems.Thm_ConleyZehnder_czIndex_determinant
import Theorems.Thm_ConleyZehnder_czIndex_eq_of_family
import Theorems.Thm_ConleyZehnder_czIndex_loop
import Theorems.Thm_ConleyZehnder_maslovValue_existsUnique
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Matrix CauchyRiemannIndex

namespace CRB1

variable {n : ℕ}

/-- The symplectic inverse `-J₀ Aᵀ J₀`. -/
def jinv (A : Mat n) : Mat n := -(J₀ n) * Aᵀ * J₀ n

lemma continuous_jinv : Continuous (jinv (n := n)) := by
  unfold jinv; fun_prop

lemma jinv_mem {A : Mat n} (hA : IsSymplectic A) : IsSymplectic (jinv A) :=
  (⟨A, hA⟩ : symplecticGroup (Fin n) ℝ)⁻¹.2

lemma mul_jinv {A : Mat n} (hA : IsSymplectic A) : A * jinv A = 1 :=
  congrArg Subtype.val (mul_inv_cancel (⟨A, hA⟩ : symplecticGroup (Fin n) ℝ))

lemma jinv_mul {A : Mat n} (hA : IsSymplectic A) : jinv A * A = 1 :=
  congrArg Subtype.val (inv_mul_cancel (⟨A, hA⟩ : symplecticGroup (Fin n) ℝ))

lemma mul_mem' {A B : Mat n} (hA : IsSymplectic A) (hB : IsSymplectic B) :
    IsSymplectic (A * B) := Submonoid.mul_mem _ hA hB

lemma jinv_one : jinv (1 : Mat n) = 1 := by
  simpa using jinv_mul (n := n) (A := 1) (Submonoid.one_mem _)

/-- The set `SP(n)`, written out. -/
def SPs (n : ℕ) : Set C(unitInterval, Mat n) :=
  {ψ | (∀ t, IsSymplectic (ψ t)) ∧ ψ 0 = 1 ∧ (1 - ψ 1).det ≠ 0}

lemma joinedIn_of_family (H : C(unitInterval × unitInterval, Mat n))
    (hH : ∀ s, H.curry s ∈ SPs n) : JoinedIn (SPs n) (H.curry 0) (H.curry 1) :=
  ⟨⟨H.curry, rfl, rfl⟩, hH⟩

/-- `s * t` on the unit interval. -/
def imul : C(unitInterval × unitInterval, unitInterval) :=
  ⟨fun p => ⟨p.1 * p.2, unitInterval.mul_mem p.1.2 p.2.2⟩, by fun_prop⟩

lemma czIndex_eq_cz (ψ : C(unitInterval, Mat n)) :
    czIndex ψ = ConleyZehnder.czIndex ψ := rfl

end CRB1

open CRB1 in
theorem solution (n : ℕ) (ψ₀ ψ₁ : C(unitInterval, Mat n))
    (hs₀ : ∀ t, IsSymplectic (ψ₀ t)) (h0₀ : ψ₀ 0 = 1) (h1₀ : (1 - ψ₀ 1).det ≠ 0)
    (hs₁ : ∀ t, IsSymplectic (ψ₁ t)) (h0₁ : ψ₁ 0 = 1) (h1₁ : (1 - ψ₁ 1).det ≠ 0)
    (h : czIndex ψ₀ = czIndex ψ₁) :
    ∃ G : C(unitInterval × unitInterval, Mat n), (∀ t, G (0, t) = ψ₀ t) ∧
      (∀ t, G (1, t) = ψ₁ t) ∧ (∀ s t, IsSymplectic (G (s, t))) ∧ (∀ s, G (s, 0) = 1) ∧
      ∀ s, (1 - G (s, 1)).det ≠ 0 := by
  -- the endpoints lie in the same component of `Sp*`
  have hsign : Real.sign (1 - ψ₁ 1).det = Real.sign (1 - ψ₀ 1).det := by
    rw [← ConleyZehnder.czIndex_determinant ψ₀ ⟨hs₀, h0₀, h1₀⟩,
      ← ConleyZehnder.czIndex_determinant ψ₁ ⟨hs₁, h0₁, h1₁⟩, ← czIndex_eq_cz,
      ← czIndex_eq_cz, h]
  have hβ := spStar_joinedIn_of_sign_det_eq n (ψ₁ 1) (ψ₀ 1) ⟨hs₁ 1, h1₁⟩ ⟨hs₀ 1, h1₀⟩ hsign
  set β := hβ.somePath with hβdef
  have hβmem : ∀ s, β s ∈ SpStar n := hβ.somePath_mem
  -- slide the endpoint of `ψ₁` along `β`
  let G₂ : C(unitInterval × unitInterval, Mat n) :=
    ⟨fun p => ψ₁ p.2 * jinv (ψ₁ 1) * β (imul p), by
      have := continuous_jinv (n := n)
      have hb : Continuous fun p : unitInterval × unitInterval => β (imul p) :=
        β.continuous.comp imul.continuous
      fun_prop⟩
  have G₂s : ∀ s t, IsSymplectic (G₂ (s, t)) := fun s t =>
    mul_mem' (mul_mem' (hs₁ t) (jinv_mem (hs₁ 1))) (hβmem _).1
  have G₂0 : ∀ s, G₂ (s, 0) = 1 := fun s => by
    show ψ₁ 0 * jinv (ψ₁ 1) * β (imul (s, 0)) = 1
    have : imul (s, 0) = 0 := Subtype.ext (by simp [imul])
    rw [this, β.source, h0₁, one_mul, jinv_mul (hs₁ 1)]
  have G₂1 : ∀ s, G₂ (s, 1) = β s := fun s => by
    show ψ₁ 1 * jinv (ψ₁ 1) * β (imul (s, 1)) = β s
    have : imul (s, 1) = s := Subtype.ext (by simp [imul])
    rw [this, mul_jinv (hs₁ 1), one_mul]
  have G₂mem : ∀ s, G₂.curry s ∈ SPs n := fun s =>
    ⟨fun t => G₂s s t, G₂0 s, by
      show (1 - G₂ (s, 1)).det ≠ 0
      rw [G₂1]; exact (hβmem s).2⟩
  set ψ₁' := G₂.curry 1 with hψ₁'
  have hψ₁'1 : ψ₁' 1 = ψ₀ 1 := by
    show G₂ (1, 1) = ψ₀ 1
    rw [G₂1, β.target]
  have e₂0 : G₂.curry 0 = ψ₁ := ContinuousMap.ext fun t => by
    show ψ₁ t * jinv (ψ₁ 1) * β (imul (0, t)) = ψ₁ t
    have : imul (0, t) = 0 := Subtype.ext (by simp [imul])
    rw [this, β.source, mul_assoc, jinv_mul (hs₁ 1), mul_one]
  have j₂ : JoinedIn (SPs n) ψ₁ ψ₁' := e₂0 ▸ joinedIn_of_family G₂ G₂mem
  have hz : czIndex ψ₁' = czIndex ψ₀ := by
    rw [czIndex_eq_cz, czIndex_eq_cz,
      ConleyZehnder.czIndex_eq_of_family G₂ G₂s G₂0 (fun s => by rw [G₂1]; exact (hβmem s).2)
        ψ₁ ψ₁' (fun t => by rw [← e₂0]; rfl) (fun t => rfl), ← czIndex_eq_cz,
      ← czIndex_eq_cz, h]
  have hs' : ∀ t, IsSymplectic (ψ₁' t) := fun t => G₂s 1 t
  -- the difference loop
  let φ : C(unitInterval, Mat n) :=
    ⟨fun t => ψ₀ t * jinv (ψ₁' t), by have := continuous_jinv (n := n); fun_prop⟩
  have φs : ∀ t, IsSymplectic (φ t) := fun t => mul_mem' (hs₀ t) (jinv_mem (hs' t))
  have φ0 : φ 0 = 1 := by
    show ψ₀ 0 * jinv (ψ₁' 0) = 1
    rw [h0₀, show ψ₁' 0 = 1 from G₂0 1, jinv_one, one_mul]
  have φ1 : φ 1 = 1 := by
    show ψ₀ 1 * jinv (ψ₁' 1) = 1
    rw [hψ₁'1, mul_jinv (hs₀ 1)]
  have φψ : φ * ψ₁' = ψ₀ := ContinuousMap.ext fun t => by
    show ψ₀ t * jinv (ψ₁' t) * ψ₁' t = ψ₀ t
    rw [mul_assoc, jinv_mul (hs' t), mul_one]
  have hloop := ConleyZehnder.czIndex_loop n φ ⟨φs, φ0, φ1⟩ ψ₁'
    ⟨hs', G₂0 1, by rw [hψ₁'1]; exact h1₀⟩
  rw [φψ, ← czIndex_eq_cz, ← czIndex_eq_cz, ← hz] at hloop
  have hm : ConleyZehnder.maslovIndex φ = 0 := by omega
  obtain ⟨k, hk, hku⟩ := ConleyZehnder.maslovValue_existsUnique φ ⟨φs, φ0, φ1⟩
  have hex : ∃ k, ConleyZehnder.IsMaslovValue φ k := ⟨k, hk⟩
  have hk0 : k = 0 := by
    rw [← hm]; unfold ConleyZehnder.maslovIndex; rw [dif_pos hex]
    exact (hku _ hex.choose_spec).symm
  obtain ⟨θ, hθ, hθ1⟩ := hk
  rw [hk0] at hθ1
  obtain ⟨Φ, Φ0, Φ1, Φs, Φt0, Φt1⟩ :=
    symplecticLoop_homotopic_one_of_rhoHat_degree_zero n φ φs φ0 φ1 θ hθ
      (by simp at hθ1; linarith)
  -- contract the difference loop
  let G₄ : C(unitInterval × unitInterval, Mat n) :=
    ⟨fun p => Φ p * ψ₁' p.2, by
      have h1 : Continuous fun p : unitInterval × unitInterval => ψ₁' p.2 :=
        ψ₁'.continuous.comp continuous_snd
      exact Φ.continuous.mul h1⟩
  have G₄mem : ∀ s, G₄.curry s ∈ SPs n := fun s =>
    ⟨fun t => mul_mem' (Φs s t) (hs' t),
     by show Φ (s, 0) * ψ₁' 0 = 1; rw [Φt0, one_mul]; exact G₂0 1,
     by show (1 - Φ (s, 1) * ψ₁' 1).det ≠ 0; rw [Φt1, one_mul, hψ₁'1]; exact h1₀⟩
  have e₄0 : G₄.curry 0 = ψ₀ := by
    rw [← φψ]; exact ContinuousMap.ext fun t => by
      show Φ (0, t) * ψ₁' t = φ t * ψ₁' t; rw [Φ0]
  have e₄1 : G₄.curry 1 = ψ₁' := ContinuousMap.ext fun t => by
    show Φ (1, t) * ψ₁' t = ψ₁' t; rw [Φ1, one_mul]
  have j₄ : JoinedIn (SPs n) ψ₀ ψ₁' := e₄0 ▸ e₄1 ▸ joinedIn_of_family G₄ G₄mem
  have j := j₄.trans j₂.symm
  refine ⟨ContinuousMap.uncurry j.somePath.toContinuousMap, fun t => ?_, fun t => ?_,
    fun s t => (j.somePath_mem s).1 t, fun s => (j.somePath_mem s).2.1,
    fun s => (j.somePath_mem s).2.2⟩
  · show j.somePath 0 t = ψ₀ t
    rw [Path.source]
  · show j.somePath 1 t = ψ₁ t
    rw [Path.target]
