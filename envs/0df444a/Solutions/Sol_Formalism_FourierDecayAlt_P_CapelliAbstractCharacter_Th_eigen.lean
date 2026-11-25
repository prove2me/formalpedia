-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.Th_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:05.456745+00:00
-- url     : https://prove2.me/submissions/a0e67c7f-8aa4-415a-989a-02667caa31b1

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_polyVanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_eval_prod_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_deg_prod_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliAbstractCharacter_Th_pol
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution (hE : GlRel E) {m : Fin (N + 1) → ℂ} {v : V} (hv : v ∈ CapSp E m) (i : Fin (N + 1))
    {Y : Fin (N + 1) → V} (hY : Y ∈ Gd E v) (hK : KK E Y = (-m i) • Y) (u : ℂ) :
    Th E u Y = (∏ j ∈ Finset.univ.erase i, (u + m j)) • Y := by
  have key : ∀ w : ℂ, w ≠ -m i → Th E w Y = (∏ j ∈ Finset.univ.erase i, (w + m j)) • Y := by
    intro w hw
    have h := star E hE hv hY w
    rw [hK, map_smul, ← sub_smul] at h
    have hne : w - -m i ≠ 0 := sub_ne_zero.mpr hw
    have hc : cpol m w = (w - -m i) * ∏ j ∈ Finset.univ.erase i, (w + m j) := by
      rw [cpol, ← Finset.mul_prod_erase Finset.univ (fun j => w + m j) (Finset.mem_univ i), sub_neg_eq_add]
    rw [hc, mul_smul] at h
    exact smul_right_injective (Fin (N + 1) → V) hne h
  obtain ⟨A, hA⟩ := Th_pol E
  have hQ : (∏ j ∈ Finset.univ.erase i, ((Polynomial.X : ℂ[X]) + C (m j))).natDegree < N + 1 := by
    have h := deg_prod_lin (Finset.univ.erase i) m
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at h
    omega
  have hev : ∀ w : ℂ, ∏ j ∈ Finset.univ.erase i, (w + m j) =
      ∑ s ∈ Finset.range (N + 1),
        (∏ j ∈ Finset.univ.erase i, ((Polynomial.X : ℂ[X]) + C (m j))).coeff s * w ^ s := by
    intro w
    rw [← eval_prod_lin, Polynomial.eval_eq_sum_range' hQ]
  have hvan := polyVanish (N + 1)
    (fun s => A s Y - (∏ j ∈ Finset.univ.erase i, ((Polynomial.X : ℂ[X]) + C (m j))).coeff s • Y) {-m i} (by
      intro w hw
      have h1 := key w (by simpa using hw)
      rw [hA, hev, Finset.sum_smul] at h1
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [sub_eq_zero, h1]
      exact Finset.sum_congr rfl (fun s _ => by rw [mul_comm, mul_smul]))
  rw [hA, hev, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have h2 := hvan s hs
  rw [sub_eq_zero] at h2
  rw [h2, mul_comm, mul_smul]
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
