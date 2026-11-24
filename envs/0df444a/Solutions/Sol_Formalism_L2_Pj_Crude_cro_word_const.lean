-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_word_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:48:48.453209+00:00
-- url     : https://prove2.me/submissions/0d21d9cd-46bc-4c68-939a-7dbbe6d6e758

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Theorems.Thm_Formalism_L2_Pj_Crude_ordGe_one_iff
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_word

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution {ι : Type} [Fintype ι] (Op Op' : ι → PS k n d → PS k n d) (m : ι →₀ ℕ)
    (hsub : ∀ l X Y, Op l (X - Y) = Op l X - Op l Y)
    (hlow : ∀ l t X, OrdGe (t + 1) X → OrdGe t (Op l X)) (hlow' : ∀ l t X, OrdGe (t + 1) X → OrdGe t (Op' l X))
    (hdiff : ∀ l t X, OrdGe (t + 1) X → OrdGe (t + 1) (Op l X - Op' l X)) (X Y : PS k n d)
    (hX : OrdGe m.degree X) (hY : OrdGe m.degree Y) (hXY : OrdGe (m.degree + 1) (X - Y)) :
    constantCoeff ((Finset.univ : Finset ι).toList.foldr (fun l g => (Op l)^[m l] g) X) =
      constantCoeff ((Finset.univ : Finset ι).toList.foldr (fun l g => (Op' l)^[m l] g) Y) := by
  have hs : ((Finset.univ : Finset ι).toList.map m).sum = m.degree := by
    have h1 : ((Finset.univ : Finset ι).toList.map m).sum = ∑ i, m i := by
      first
        | exact Finset.sum_map_toList _ _
        | exact Finset.sum_toList _ _
        | simp [Finset.sum_map_toList]
        | simp
    rw [h1]
    first
      | exact (Finsupp.degree_eq_sum m).symm
      | (unfold Finsupp.degree; exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by simpa using hi).symm)
  have hX' : OrdGe (((Finset.univ : Finset ι).toList.map m).sum + 0) X := by rw [hs, add_zero]; exact hX
  have hY' : OrdGe (((Finset.univ : Finset ι).toList.map m).sum + 0) Y := by rw [hs, add_zero]; exact hY
  have hXY' : OrdGe (((Finset.univ : Finset ι).toList.map m).sum + 0 + 1) (X - Y) := by
    rw [hs, add_zero]; exact hXY
  obtain ⟨-, -, h⟩ := cro_word Op Op' m hsub hlow hlow' hdiff _ 0 X Y hX' hY' hXY'
  rw [zero_add, ordGe_one_iff, map_sub, sub_eq_zero] at h
  exact h
end Formalism.L2.Pj.Crude
