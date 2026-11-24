-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:50:41.632861+00:00
-- url     : https://prove2.me/submissions/268adf4f-4be7-4cbe-9d9e-70ad1b0ca23b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {m : ℕ} (hm : m + 2 < k + 1) (cs : Fin m → Fin (2 * r + k + 1) → ℂ)
    (a b : Fin (2 * r + k + 1) → ℂ) :
    ∃ v, v ≠ 0 ∧ inWb k r v ∧ herm (Hpk k r) v a = 0 ∧ herm (Hpk k r) v b = 0 ∧
      ∀ j, herm (Hpk k r) v (cs j) = 0 := by
  classical
  obtain ⟨c, hca, hcb, hcs⟩ : ∃ c : Fin (m + 2) → Fin (2 * r + k + 1) → ℂ,
      c 0 = a ∧ c (Fin.succ 0) = b ∧ ∀ j : Fin m, c j.succ.succ = cs j :=
    ⟨Fin.cons a (Fin.cons b cs), by simp, by simp, fun j => by simp⟩
  obtain ⟨emb, hemb⟩ : ∃ emb : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ),
      ∀ x, emb x = Function.extend (wI k r) x 0 :=
    ⟨Function.ExtendByZero.linearMap ℂ (wI k r), fun x => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : (Fin (k + 1) → ℂ) →ₗ[ℂ] (Fin (m + 2) → ℂ),
      ∀ x j, L x j = herm (Hpk k r) (emb x) (c j) :=
    ⟨(LinearMap.pi fun j => gbL (c j)) ∘ₗ emb, fun x j => rfl⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker L
  have hle : Module.finrank ℂ (LinearMap.range L) ≤ m + 2 := by
    have h1 := Submodule.finrank_le (LinearMap.range L)
    simpa using h1
  simp only [Module.finrank_fin_fun] at hrk
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker L) := by omega
  obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hx0' : x ≠ 0 := fun h => hx0 (by subst h; rfl)
  have hL0 : ∀ j, herm (Hpk k r) (emb x) (c j) = 0 := by
    intro j
    have h1 := congrFun (LinearMap.mem_ker.1 hx) j
    rw [hL] at h1
    exact h1
  have hinj : Function.Injective (wI k r) := by
    intro p q h
    simp only [wI, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  refine ⟨emb x, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply hx0'
    funext j
    have h1 := congrFun h0 (wI k r j)
    rw [hemb, hinj.extend_apply] at h1
    simpa using h1
  · intro i hi
    have hni : ¬∃ p, wI k r p = i := by
      rintro ⟨p, rfl⟩
      have := p.isLt
      simp only [wI, Fin.val_mk] at hi
      omega
    rw [hemb, Function.extend_apply' _ _ _ hni, Pi.zero_apply]
  · have h1 := hL0 0
    rwa [hca] at h1
  · have h1 := hL0 (Fin.succ 0)
    rwa [hcb] at h1
  · intro j
    have h1 := hL0 j.succ.succ
    rwa [hcs] at h1
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
