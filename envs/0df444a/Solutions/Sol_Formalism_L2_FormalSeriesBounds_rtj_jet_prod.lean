-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_jet_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:42.410649+00:00
-- url     : https://prove2.me/submissions/863aaaab-c18a-4ebc-9aed-4852a843d46c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_serIn_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_serIn_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {ι : Type} (A : ι → Set σ) (s : Finset ι)
    (hA : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j))
    (P : ι → MvPolynomial σ K) (F : ι → MvPowerSeries σ K)
    (hP : ∀ i ∈ s, P i ∈ MvPolynomial.supported K (A i)) (hF : ∀ i ∈ s, rtjSerIn (A i) (F i)) :
    jetAt0 (∏ i ∈ s, P i) (∏ i ∈ s, F i) = ∏ i ∈ s, jetAt0 (P i) (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Finset.prod_empty]
    exact rtj_jet_one
  | insert i t hi ih =>
    have hA' : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → Disjoint (A a) (A b) := fun a ha b hb hab =>
      hA a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb) hab
    have hsub : ∀ j ∈ t, A j ⊆ (A i)ᶜ := by
      intro j hj x hx hxi
      have hij : i ≠ j := by
        rintro rfl
        exact hi hj
      exact Set.disjoint_left.mp
        (hA i (Finset.mem_insert_self i t) j (Finset.mem_insert_of_mem hj) hij) hxi hx
    have hPt : (∏ j ∈ t, P j) ∈ MvPolynomial.supported K (A i)ᶜ :=
      prod_mem fun j hj => MvPolynomial.supported_mono (hsub j hj) (hP j (Finset.mem_insert_of_mem hj))
    have hFt : rtjSerIn (A i)ᶜ (∏ j ∈ t, F j) :=
      rtj_serIn_prod (A i)ᶜ t F fun j hj => rtj_serIn_mono (hsub j hj) (hF j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi,
      rtj_jet_mul (A i) (P i) _ (F i) _ (hP i (Finset.mem_insert_self i t)) hPt
        (hF i (Finset.mem_insert_self i t)) hFt,
      ih hA' (fun j hj => hP j (Finset.mem_insert_of_mem hj))
        (fun j hj => hF j (Finset.mem_insert_of_mem hj))]
end Formalism.L2.FormalSeriesBounds
