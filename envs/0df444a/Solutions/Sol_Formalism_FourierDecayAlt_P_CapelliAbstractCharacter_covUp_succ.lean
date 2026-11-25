-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.covUp_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:45.784735+00:00
-- url     : https://prove2.me/submissions/e06cd249-100f-4713-8614-de37c31aa7a5

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_aeval_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_Th_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_mem_Gd
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_detCov
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_basis_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_KK_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_charId
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_Th_eigen
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_REAL_charId


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution (η : Fin (N + 1) → Module.End ℂ V) (hE : GlRel E) (hη : IsCov E η) (m : Fin (N + 1) → ℂ)
    (hm : Function.Injective m) (v : V) (hv : v ∈ CapSp E m) :
    ∃ Ψ : Fin (N + 1) → Fin (N + 1) → V,
      (∀ x, ∑ i, Ψ i x = η x v) ∧
      (∀ i x, Ψ i x ∈ CapSp E (Function.update m i (m i + 1))) ∧
      ∀ (i x : Fin (N + 1)) (u : ℂ),
        ∑ a : Fin (N + 1), ((-1 : ℂ) ^ ((a : ℕ) + (x : ℕ))) • qminor E a.succAbove x.succAbove u (Ψ i a) =
          (∏ j ∈ Finset.univ.erase i, (u + m j)) • Ψ i x := by
  obtain ⟨Z, hZdef⟩ : ∃ Z : Fin (N + 1) → V, Z = fun x => η x v := ⟨_, rfl⟩
  have hZ : Z ∈ Gd E v := (mem_Gd E).mpr ⟨η, hη, fun j => by rw [hZdef]⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : Fin (N + 1) → Fin (N + 1) → V,
      Y = fun i => Polynomial.aeval (KK E) (Lagrange.basis Finset.univ (fun j => -m j) i) Z := ⟨_, rfl⟩
  have hY : ∀ i, Y i ∈ Gd E v := by
    intro i
    rw [hYdef]
    exact aeval_mem (Gd E v) (KK E) (fun W hW => KK_mem E hE hW) _ Z hZ
  have hKY : ∀ i, KK E (Y i) = (-m i) • Y i := by
    intro i
    obtain ⟨w, hw⟩ := basis_mul m i
    have h1 : Polynomial.aeval (KK E)
        (((Polynomial.X : ℂ[X]) + C (m i)) * Lagrange.basis Finset.univ (fun j => -m j) i) Z = 0 := by
      rw [hw, map_mul, Polynomial.aeval_C]
      first
        | rw [Module.End.mul_apply, charId E hE hv Z hZ, map_zero]
        | rw [LinearMap.mul_apply, charId E hE hv Z hZ, map_zero]
    rw [map_mul] at h1
    first
      | rw [Module.End.mul_apply] at h1
      | rw [LinearMap.mul_apply] at h1
    rw [map_add, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.add_apply,
      Module.algebraMap_end_apply] at h1
    rw [hYdef, neg_smul]
    exact eq_neg_of_add_eq_zero_left h1
  refine ⟨Y, fun x => ?_, fun i x => ?_, fun i x u => ?_⟩
  · have hs : ∑ i, Lagrange.basis Finset.univ (fun j => -m j) i = 1 :=
      Lagrange.sum_basis (fun a _ b _ h => hm (neg_injective h)) Finset.univ_nonempty
    have hsum : ∑ i, Y i = Z := by
      rw [hYdef, ← LinearMap.sum_apply, ← map_sum, hs, map_one]
      rfl
    have h1 := congrFun hsum x
    rw [Finset.sum_apply] at h1
    rw [h1, hZdef]
  · rw [CapSp, Submodule.mem_iInf]
    intro w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero]
    first
      | rw [Module.End.one_apply]
      | rw [LinearMap.one_apply]
    rw [detCov E hE hv (hY i) w x, Th_eigen E hE hv i (hY i) (hKY i) w, Pi.smul_apply, ← add_smul]
    congr 1
    have hP : ∏ j ∈ Finset.univ.erase i, (w + Function.update m i (m i + 1) j) =
        ∏ j ∈ Finset.univ.erase i, (w + m j) :=
      Finset.prod_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
    have hi : Function.update m i (m i + 1) i = m i + 1 := by simp
    have e1 := Finset.mul_prod_erase Finset.univ (fun j => w + m j) (Finset.mem_univ i)
    have e2 := Finset.mul_prod_erase Finset.univ (fun j => w + Function.update m i (m i + 1) j) (Finset.mem_univ i)
    beta_reduce at e1 e2
    rw [cpol, cpol, ← e1, ← e2, hP, hi]
    ring
  · rw [← Th_apply, Th_eigen E hE hv i (hY i) (hKY i) u, Pi.smul_apply]
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
