-- Prove2me | solution 1 for BrooksTheorem.Aux.exists_proper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:44:52.952931+00:00
-- url     : https://prove2.me/submissions/d30cc81d-73d8-411f-a438-b7e3d767521c

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_step

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution (k : ℕ) (hk : 3 ≤ k) (H : SimpleGraph V)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) :
    ∃ f : V → Fin k, Proper H f := by
  suffices h : ∀ n, ∀ H : SimpleGraph V, mu H = n → (∀ v, (nb H v).card ≤ k) →
      H.CliqueFree (k + 1) → ∃ f : V → Fin k, Proper H f from h _ H rfl hdeg hcf
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro H hn hdeg hcf
    exact step hk (fun H' hlt hdeg' hcf' => ihn _ (hn ▸ hlt) H' rfl hdeg' hcf') hdeg hcf
end BrooksTheorem.Aux
