-- Prove2me | solution 1 for DeciSigma1.Constraints.Ranked.Extension.upperAt_sink
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:02:52.058798+00:00
-- url     : https://prove2.me/submissions/8858739e-d152-496b-ab68-45667489714f

module
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_RankedExtensions
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_not_sink_original
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_derives_out_of_sink

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Ranked
variable {n k m : ℕ}
variable {Γ : List (LitT n (Fin k))} {ψ : List (LitT n (Fin (k + m)))}
  {Source Sink : Fin (k + m) → Prop} {rank : Fin (k + m) → ℕ}
namespace DeciSigma1.Constraints.Ranked
namespace Extension
theorem _root_.solution (e : Extension Γ ψ Source Sink rank)
    {π : List (Fin n)} {a b : Fin (k + m)} (h : UpperAt ψ π a b)
    (ha : Sink a) : Sink b ∧ rank a ≤ rank b ∧ (π ≠ [] → rank a < rank b) := by
  induction h with
  | nil hd =>
    have he := e.derives_out_of_sink hd ha
    subst he
    exact ⟨ha, le_rfl, fun hn => False.elim (hn rfl)⟩
  | @cons a z c b π i hd hl hp ih =>
    have he := e.derives_out_of_sink hd ha
    subst z
    rcases e.upper _ _ hl with ⟨z', c', _, rfl, _⟩ | ⟨hc, _⟩
    · exact False.elim (e.not_sink_original z' ha)
    · obtain ⟨hb, hle, _⟩ := ih (hc i).1
      have hlt := (hc i).2
      exact ⟨hb, (lt_of_lt_of_le hlt hle).le, fun _ => lt_of_lt_of_le hlt hle⟩
end Extension
end DeciSigma1.Constraints.Ranked
