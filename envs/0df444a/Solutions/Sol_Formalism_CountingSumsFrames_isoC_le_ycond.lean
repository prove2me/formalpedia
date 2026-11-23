-- Prove2me | solution 1 for Formalism.CountingSumsFrames.isoC_le_ycond
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:02.938795+00:00
-- url     : https://prove2.me/submissions/e343844c-8b37-4984-b6ae-e33063bb718c

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_cartan_eig
import Theorems.Thm_Formalism_CountingSumsFrames_lower_action_preserves_weight_le
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_comm
import Theorems.Thm_Formalism_CountingSumsFrames_isoC_glStable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (la : Fin r → ℤ) (Mt : WithTop ℤ)
    (hla : ((la 0 : ℤ) : WithTop ℤ) ≤ Mt) : IsoC p LL j univ la ≤ YCond p (r := r) LL j Mt := by
  set Lo : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    sInf {S | HWC p LL j univ la ≤ S ∧ ∀ c d : Fin r, d < c → ∀ x ∈ S, glAct p LL j c d x ∈ S} with hLo
  have hHLo : HWC p LL j univ la ≤ Lo := le_sInf fun _ hS => hS.1
  have hlow : ∀ c d : Fin r, d < c → ∀ x ∈ Lo, glAct p LL j c d x ∈ Lo := by
    intro c d hdc x hx
    rw [hLo, Submodule.mem_sInf] at hx ⊢
    intro S hS
    exact hS.2 c d hdc x (hx S hS)
  have hLoW : Lo ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ((la 0 : ℤ) : WithTop ℤ)} := by
    refine sInf_le ⟨?_, fun c d hdc => lower_action_preserves_weight_le LL j c d hdc _⟩
    intro x hx
    have hw := (Submodule.mem_inf.mp hx).1
    rw [WtSpC, mem_restrictSupport_iff] at hw
    rw [mem_restrictSupport_iff]
    intro m hm
    have := hw hm 0 (Finset.mem_univ _)
    simp only [Set.mem_ofPred_eq]
    rw [this]
  have hgl : ∀ c d : Fin r, ∀ x ∈ Lo, glAct p LL j c d x ∈ Lo := by
    set L' : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
      Lo ⊓ ⨅ (c : Fin r) (d : Fin r), Lo.comap (glAct p LL j c d) with hL'
    have hmemL' : ∀ x, x ∈ L' ↔ x ∈ Lo ∧ ∀ c d, glAct p LL j c d x ∈ Lo := by
      intro x
      simp only [hL', Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
    have hle : Lo ≤ L' := by
      refine sInf_le ⟨?_, ?_⟩
      · intro h hh
        rw [hmemL']
        refine ⟨hHLo hh, fun c d => ?_⟩
        rcases lt_trichotomy c d with hcd | hcd | hcd
        · have hk := (Submodule.mem_inf.mp hh).2
          simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hk
          rw [hk c d ⟨Finset.mem_univ _, Finset.mem_univ _, hcd⟩]
          exact Lo.zero_mem
        · subst hcd
          rw [cartan_eig LL j la h (Submodule.mem_inf.mp hh).1 c]
          exact Lo.smul_mem _ (hHLo hh)
        · exact hlow c d hcd h (hHLo hh)
      · intro a b hba x hx
        rw [hmemL'] at hx ⊢
        refine ⟨hlow a b hba x hx.1, fun c d => ?_⟩
        have hcomm := glAct_comm LL j c d a b x
        have e : glAct p LL j c d (glAct p LL j a b x) = glAct p LL j a b (glAct p LL j c d x) +
            ((if d = a then glAct p LL j c b x else 0) - (if b = c then glAct p LL j a d x else 0)) := by
          rw [← hcomm]; abel
        rw [e]
        refine Lo.add_mem (hlow a b hba _ (hx.2 c d)) (Lo.sub_mem ?_ ?_)
        · split_ifs
          · exact hx.2 c b
          · exact Lo.zero_mem
        · split_ifs
          · exact hx.2 a d
          · exact Lo.zero_mem
    intro c d x hx
    exact ((hmemL' x).mp (hle hx)).2 c d
  have hIso : IsoC p LL j univ la ≤ Lo :=
    sInf_le ⟨hHLo, fun c _ d _ x hx => hgl c d x hx⟩
  refine le_sSup ⟨?_, ?_⟩
  · intro x hx
    have h1 := hLoW (hIso hx)
    rw [mem_restrictSupport_iff] at h1 ⊢
    intro m hm
    exact le_trans (h1 hm) hla
  · intro c d x hx
    exact isoC_glStable LL j la c d x hx
end Formalism.CountingSumsFrames
