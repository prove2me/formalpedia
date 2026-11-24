-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BruhatBigCell.sum_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:12:36.231204+00:00
-- url     : https://prove2.me/submissions/e1255ed3-a5e5-4dc1-ab6c-9c5d4213f785

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.BruhatBigCell
open GBasic
variable {k r : ℕ}
variable (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
namespace Formalism.QuantumDeterminants.BruhatBigCell
theorem _root_.solution (f : Fin (2 * r + k + 1) → ℂ)
    (hf : ∀ p : Fin (2 * r + k + 1), (p.val < r ∨ r + k < p.val) → f p = 0) :
    ∑ p, f p = ∑ q : Fin (k + 1), f (wI k r q) := by
  have emb : Function.Injective (wI k r) := by
    intro a b h; apply Fin.ext; have := congrArg Fin.val h; simp only [wI] at this; omega
  have hm : ∑ q : Fin (k + 1), f (wI k r q) = ∑ x ∈ Finset.univ.map ⟨wI k r, emb⟩, f x := by
    rw [Finset.sum_map]; rfl
  rw [hm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  apply hf
  by_contra hlt
  push Not at hlt
  exact hp (Finset.mem_map.2 ⟨⟨p.val - r, by omega⟩, Finset.mem_univ _,
    Fin.ext (by show r + (p.val - r) = p.val; omega)⟩)
end Formalism.QuantumDeterminants.BruhatBigCell
