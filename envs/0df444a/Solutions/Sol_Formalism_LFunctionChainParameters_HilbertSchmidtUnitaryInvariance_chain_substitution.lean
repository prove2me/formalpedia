-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.chain_substitution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:20:14.53738+00:00
-- url     : https://prove2.me/submissions/dba0ed72-09f0-4b01-8e06-48ab78805bbf

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_twist_invariance
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_dim
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Wfr_mul
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_Wfr_uni
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_isUni_one
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_wordCount_valid
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_corollary_chain
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_twist_ramified_factor
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_KpG_BfS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module NumberField
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
theorem _root_.solution : ChainCondition := by
  intro ι _ Dall D D1 d r Pf Vr ga c V U J J1 A Y' Y Dstar sg η0 η1 e0 de del C0 Gam h
  obtain ⟨c1, c2, -, -, -, c5, -, c7, -, -, -, c11⟩ :=
    corollary_chain ι Dall D D1 d r Pf Vr ga c V U J J1 A Y' Y Dstar sg η0 η1 e0 de del C0 Gam h
  obtain ⟨hga, hDs, hs, hs20, hC, hG, hcard, hd, a1, a2, a3, a4, a5, hS, hVr, hde0, hde, hcor, hc,
    hV, hU, hJ, hdel, hD, -, -, hMI⟩ := h
  have hR := wordCount_valid ι d C0 Gam sg Dstar hC hG hs hDs.le hcard hd
  obtain ⟨-, t2, -⟩ := twist_ramified_factor ι Dall (D + D1) d r Pf Vr ga c V U (Wfr J J1) hc hV hU
    (Wfr_uni J J1 hJ) hVr
  obtain ⟨-, -, -, i3⟩ := twist_invariance ι Dall Dall d Pf ga c V (fun _ => 1) hc hV
    (fun _ => isUni_one _)
  have hRs : MatrixLatticeEstimates.RsG (fun u => Fin (d u)) = Rs d := by simp [MatrixLatticeEstimates.RsG, Rs]
  have hrel : ∀ u i j, (BfS Pf c V J J1 u * VrS Vr U u) i j
      = Brow (Wfr J J1) (Btwist (Bram Pf Vr) c V U) u (finSumFinEquiv i) j := by
    intro u i j
    have e1 : BfS Pf c V J J1 u * VrS Vr U u
        = Matrix.fromRows Jᴴ J1ᴴ * Btwist (Bram Pf Vr) c V U u := by
      unfold BfS VrS WfrS Btwist Bram
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    unfold Brow
    rw [e1, Wfr_mul, ← Matrix.fromRows_mul]
    simp
  refine ⟨c1, t2, by rw [hRs]; exact hR, by simpa only [Fintype.card_fin, hRs] using hcor, ?_,
    fun u k j => ?_, hrel, ?_, c11, hdel, ?_⟩
  · have hS' := (i3 Dstar η0 η1 e0).mpr hS
    refine ⟨fun u u' hne => ?_, fun u => ?_, ?_⟩
    · rw [KpG_BfS Pf c V J J1 hJ]
      simpa only [Fintype.card_fin] using hS'.1 u u' hne
    · unfold MatrixLatticeEstimates.KdG
      rw [KpG_BfS Pf c V J J1 hJ]
      have h1 := hS'.2.1 u
      unfold Kd at h1
      simpa only [Fintype.card_fin] using h1
    · have : (Fintype.card (Fin D ⊕ Fin D1) : ℝ) = (Dall : ℝ) := by
        rw [frame_dim J J1 hJ]; simp
      rw [this]; exact hS'.2.2
  · rw [hrel, finSumFinEquiv_apply_left]
    exact c2 u k j
  · have : ((∑ u, Fintype.card (Fin (r u)) : ℕ) : ℝ) = Rs r := by simp [Rs]
    have h2 : (0 : ℝ) < ((∑ u, Fintype.card (Fin (r u)) : ℕ) : ℝ) := by rw [this]; exact c7
    exact_mod_cast h2
  · simpa using c5
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
