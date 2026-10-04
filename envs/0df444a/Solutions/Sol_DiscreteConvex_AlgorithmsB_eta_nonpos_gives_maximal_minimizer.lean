-- Prove2me | solution 1 for DiscreteConvex.AlgorithmsB.eta_nonpos_gives_maximal_minimizer
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:11:48.128183+00:00
-- url     : https://prove2.me/submissions/4ec1f940-afe0-43f3-82a1-38fc5fe800ba

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsMaximalMinimizer
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsMinimizerOf
import Definitions.Def_DiscreteConvex_AlgorithmsB_Eta

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.AlgorithmsB

namespace EtaCex

/-- `ρ(∅) = ρ({true,false}) = 0`, `ρ({true}) = -1`, `ρ({false}) = 1`. -/
def rho (X : Finset Bool) : ℤ :=
  (if true ∈ X then -1 else 0) + (if false ∈ X then 1 else 0)

theorem rho_sub : Submodular rho := by
  refine ⟨by decide, ?_⟩
  decide

def Gamma : Unit → Finset Bool := fun _ => Finset.univ

theorem eta_le : Eta rho Gamma ∅ (fun _ _ => False) ≤ 0 := by
  unfold Eta
  refine Finset.sup'_le _ _ ?_
  intro u _
  have hR : ReachSet (fun _ _ => False) u = Finset.univ := by
    ext w
    simp only [ReachSet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases u; cases w; exact Relation.ReflTransGen.refl
  rw [hR]
  have he : (Finset.univ : Finset Unit).erase u = ∅ := by
    cases u; decide
  rw [he]
  simp [RhoTilde, GammaSet, Gamma, rho]

theorem not_max : ¬ IsMaximalMinimizer rho (Finset.univ \ ∅) := by
  rintro ⟨h, -⟩
  have := h {true}
  revert this
  decide

end EtaCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V] {U : Type} [Fintype U]
    [DecidableEq U] [Nonempty U]
    (rho : Finset V → ℤ) (hrho : Submodular rho) (Gamma : U → Finset V) (Z H : Finset V)
    (hpart1 : ∀ u, Gamma u ⊆ Finset.univ \ (Z ∪ H)) (hpart2 : ∀ u, (Gamma u).Nonempty)
    (hpart3 : ∀ u v, u ≠ v → Disjoint (Gamma u) (Gamma v))
    (hpart4 : Finset.univ = (Finset.univ.biUnion Gamma) ∪ Z ∪ H) (F : U → U → Prop)
    (hinvH : ∀ W, IsMinimizerOf rho W → Disjoint H W)
    (hinvZ : ∀ W, IsMinimizerOf rho W → Z ⊆ W)
    (hinvF : ∀ u w, F u w → ∀ W, IsMinimizerOf rho W → Gamma u ⊆ W → Gamma w ⊆ W)
    (heta : Eta rho Gamma Z F ≤ 0),
    IsMaximalMinimizer rho (Finset.univ \ H)) := by
  intro h
  apply EtaCex.not_max
  refine h EtaCex.rho EtaCex.rho_sub EtaCex.Gamma ∅ ∅ ?_ ?_ ?_ ?_ (fun _ _ => False) ?_ ?_ ?_
    EtaCex.eta_le
  · intro u; simp [EtaCex.Gamma]
  · intro u; exact Finset.univ_nonempty
  · intro u v huv; exact absurd (Subsingleton.elim u v) huv
  · simp [EtaCex.Gamma]
  · intro W _; exact Finset.disjoint_empty_left W
  · intro W _; exact Finset.empty_subset W
  · intro u w huw; exact huw.elim

#print axioms solution
