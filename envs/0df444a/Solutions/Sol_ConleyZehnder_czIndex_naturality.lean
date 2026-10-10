-- Prove2me | solution 1 for ConleyZehnder.czIndex_naturality
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T21:34:33.685735+00:00
-- url     : https://prove2.me/submissions/468fa177-41ce-4a4c-a02f-d6c109be26de

import Theorems.Thm_ConleyZehnder_czIndex_eq_of_family
import Theorems.Thm_ConleyZehnder_symplectic_joined_one

open ConleyZehnder Matrix

namespace CZ10

variable {n : ℕ}

theorem inv_eq (A : Mat n) (hA : IsSymplectic A) : A⁻¹ = -J₀ n * Aᵀ * J₀ n :=
  SymplecticGroup.inv_eq_symplectic_inv A hA

theorem inv_symp (A : Mat n) (hA : IsSymplectic A) : IsSymplectic A⁻¹ := by
  rw [inv_eq A hA]; exact (⟨A, hA⟩⁻¹ : Matrix.symplecticGroup (Fin n) ℝ).2

theorem mul_inv (A : Mat n) (hA : IsSymplectic A) : A * A⁻¹ = 1 := by
  rw [mul_eq_one_comm, inv_eq A hA]
  have := SymplecticGroup.inv_left_mul_aux hA
  rw [← this]; simp only [Matrix.neg_mul]

theorem conj_symp (g A : Mat n) (hg : IsSymplectic g) (hA : IsSymplectic A) :
    IsSymplectic (g * A * g⁻¹) :=
  Submonoid.mul_mem _ (Submonoid.mul_mem _ hg hA) (inv_symp g hg)

theorem conj_det (g A : Mat n) (hg : IsSymplectic g) :
    (1 - g * A * g⁻¹).det = (1 - A).det := by
  have h : 1 - g * A * g⁻¹ = g * (1 - A) * g⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mul_inv g hg]
  rw [h, det_mul, det_mul, mul_comm (det g), mul_assoc, ← det_mul, mul_inv g hg, det_one, mul_one]

theorem cont_conj {X : Type*} [TopologicalSpace X] (g A : X → Mat n)
    (hg : Continuous g) (hA : Continuous A) (hs : ∀ x, IsSymplectic (g x)) :
    Continuous fun x => g x * A x * (g x)⁻¹ := by
  have : (fun x => (g x)⁻¹) = fun x => -J₀ n * (g x)ᵀ * J₀ n := funext fun x => inv_eq _ (hs x)
  have hi : Continuous fun x => (g x)⁻¹ := by
    rw [this]; exact (continuous_const.mul hg.matrix_transpose).mul continuous_const
  exact (hg.mul hA).mul hi

noncomputable section

/-- The family `(s, t) ↦ g (s) ψ (t) g (s)⁻¹` for a path `g`, as a continuous map. -/
def fam (g : unitInterval × unitInterval → Mat n) (ψ : C(unitInterval, Mat n))
    (hg : Continuous g) (hs : ∀ p, IsSymplectic (g p)) :
    C(unitInterval × unitInterval, Mat n) :=
  ⟨fun p => g p * ψ p.2 * (g p)⁻¹, cont_conj g (fun p => ψ p.2) hg (ψ.continuous.comp
    continuous_snd) hs⟩

theorem fam_family (g : unitInterval × unitInterval → Mat n) (ψ : C(unitInterval, Mat n))
    (hψ : ψ ∈ SP n) (hg : Continuous g) (hs : ∀ p, IsSymplectic (g p)) :
    (∀ s t, IsSymplectic (fam g ψ hg hs (s, t))) ∧ (∀ s, fam g ψ hg hs (s, 0) = 1) ∧
      (∀ s, (1 - fam g ψ hg hs (s, 1)).det ≠ 0) := by
  refine ⟨fun s t => conj_symp _ _ (hs _) (hψ.1 t), fun s => ?_, fun s => ?_⟩
  · show g (s, 0) * ψ 0 * (g (s, 0))⁻¹ = 1
    rw [hψ.2.1, Matrix.mul_one, mul_inv _ (hs _)]
  · show (1 - g (s, 1) * ψ 1 * (g (s, 1))⁻¹).det ≠ 0
    rw [conj_det _ _ (hs _)]; exact hψ.2.2

end

end CZ10

open CZ10

theorem solution {n : ℕ} (φ : C(unitInterval, Mat n))
    (hφ : ∀ t, IsSymplectic (φ t)) (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n)
    (ψ' : C(unitInterval, Mat n)) (hψ' : ∀ t, ψ' t = φ t * ψ t * (φ t)⁻¹) :
    czIndex ψ' = czIndex ψ := by
  set P := φ 0
  -- `ψ` conjugated by the constant matrix `P`
  let ψP : C(unitInterval, Mat n) :=
    ⟨fun t => P * ψ t * P⁻¹, cont_conj (fun _ => P) ψ continuous_const ψ.continuous
      (fun _ => hφ 0)⟩
  -- family 1: `φ (s t) ψ (t) φ (s t)⁻¹`
  let g₁ : unitInterval × unitInterval → Mat n :=
    fun p => φ ⟨(p.1 : ℝ) * p.2, unitInterval.mul_mem p.1.2 p.2.2⟩
  have hg₁ : Continuous g₁ := φ.continuous.comp
    (((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _)
  have hs₁ : ∀ p, IsSymplectic (g₁ p) := fun p => hφ _
  obtain ⟨a₁, b₁, c₁⟩ := fam_family g₁ ψ hψ hg₁ hs₁
  have e₁ := czIndex_eq_of_family (fam g₁ ψ hg₁ hs₁) a₁ b₁ c₁ ψP ψ'
    (fun t => by
      show P * ψ t * P⁻¹ = g₁ (0, t) * ψ t * (g₁ (0, t))⁻¹
      have : g₁ (0, t) = P := congrArg φ (Subtype.ext (by simp))
      rw [this])
    (fun t => by
      show ψ' t = g₁ (1, t) * ψ t * (g₁ (1, t))⁻¹
      have : g₁ (1, t) = φ t := congrArg φ (Subtype.ext (by simp))
      rw [this, hψ'])
  -- family 2: `γ (s) ψ (t) γ (s)⁻¹` with `γ` joining `Id` to `P`
  obtain ⟨γ, hγ0, hγ1, hγs⟩ := symplectic_joined_one P (hφ 0)
  let g₂ : unitInterval × unitInterval → Mat n := fun p => γ p.1
  have hg₂ : Continuous g₂ := γ.continuous.comp continuous_fst
  have hs₂ : ∀ p, IsSymplectic (g₂ p) := fun p => hγs _
  obtain ⟨a₂, b₂, c₂⟩ := fam_family g₂ ψ hψ hg₂ hs₂
  have e₂ := czIndex_eq_of_family (fam g₂ ψ hg₂ hs₂) a₂ b₂ c₂ ψ ψP
    (fun t => by
      show ψ t = γ 0 * ψ t * (γ 0)⁻¹
      rw [hγ0, Matrix.one_mul, inv_one, Matrix.mul_one])
    (fun t => by
      show P * ψ t * P⁻¹ = γ 1 * ψ t * (γ 1)⁻¹
      rw [hγ1])
  rw [e₁, e₂]
