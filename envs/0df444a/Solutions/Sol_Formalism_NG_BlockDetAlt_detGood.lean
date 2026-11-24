-- Prove2me | solution 1 for Formalism.NG.BlockDetAlt.detGood
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:39:49.458174+00:00
-- url     : https://prove2.me/submissions/40d55317-5e36-4f6e-9ff9-af6aae08732f

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
import Theorems.Thm_Formalism_NG_BlockDetAlt_mem_Fr
import Theorems.Thm_Formalism_NG_BlockDetAlt_coeff_psi
import Theorems.Thm_Formalism_NG_BlockDetAlt_coeff_det_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
variable {d : Type} [Fintype d] [DecidableEq d]
variable {d : Type} [Fintype d] [DecidableEq d]
namespace Formalism.NG.BlockDetAlt
theorem _root_.solution (T' : Subalgebra O (X' → O)) (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (hyp : HypDet T' R') {a : Matrix d d (PowerSeries (X' → FractionRing O))}
    (ha : a ∈ goodM R') : a.det ∈ goodS T' := by
  classical
  show ∀ n, PowerSeries.coeff n a.det ∈ Fr T'
  intro n
  let r : Fin (n + Fintype.card d) → R' := fun j => ⟨coefMat j.1 a, ha j.1⟩
  choose F hF hFx using fun e : Fin (n + Fintype.card d) →₀ ℕ => hyp (n + Fintype.card d) r e
  refine mem_Fr.2 ⟨∑ e ∈ Finset.Iic (bnd (n + Fintype.card d)),
    if wt e = n + Fintype.card d then F e else 0, ?_, fun x' => ?_⟩
  · refine Subalgebra.sum_mem _ fun e _ => ?_
    split_ifs
    · exact hF e
    · exact Subalgebra.zero_mem _
  · rw [coeff_det_eq R' a ha n x', coeff_psi, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : wt e = n + Fintype.card d
    · rw [if_pos h, if_pos h]
      exact hFx e x'
    · rw [if_neg h, if_neg h]
      simp
end Formalism.NG.BlockDetAlt
