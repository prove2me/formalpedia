-- Prove2me | solution 1 for DeciSigma1.Full.Logic.holds_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:18:34.176994+00:00
-- url     : https://prove2.me/submissions/ca0ffaac-f689-448f-9e89-31e0493256d0

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Full_Logic
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_antisymm
public import Theorems.Thm_DeciSigma1_Semantics_treeLe_refl


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Logic
open DeciSigma1.Constraints DeciSigma1.Semantics DeciSigma1.Full.Models
variable {n : ℕ} {V W : Type}
variable (c : Fin n → Bool)
namespace DeciSigma1.Full.Logic
theorem _root_.solution (ρ : V → Tree n) (s t : Term n V) :
    (DeciSigma1.Logic.QuantifierFreeFormula.eq s t).Holds (interpretation c) ρ ↔
      s.eval ρ = t.eval ρ := by
  change Tree.Le c (s.eval ρ) (t.eval ρ) ∧ Tree.Le c (t.eval ρ) (s.eval ρ) ↔ _
  exact ⟨fun h => treeLe_antisymm h.1 h.2, fun h => h ▸ ⟨treeLe_refl c _, treeLe_refl c _⟩⟩
end DeciSigma1.Full.Logic
