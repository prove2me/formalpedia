-- Prove2me | solution 1 for BondySimonovits.iterate_par_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:04:18.596416+00:00
-- url     : https://prove2.me/submissions/663e227b-561c-43ee-ba26-12ba09c0b76b

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Definitions.Def_BondySimonovitsLib_BSLayers

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V)
variable {K} {par : V → V} {x : V}
  (hpar : ∀ v, K.Reachable x v → 0 < K.dist x v →
    K.Adj v (par v) ∧ K.dist x (par v) + 1 = K.dist x v)
include hpar
namespace BondySimonovits
theorem _root_.solution : ∀ (n : ℕ) (v : V), K.Reachable x v → n ≤ K.dist x v →
    K.Reachable x (par^[n] v) ∧ K.dist x (par^[n] v) = K.dist x v - n := by
  intro n
  induction n with
  | zero => intro v hr _; simpa using hr
  | succ n ih =>
    intro v hr hn
    obtain ⟨hadj, hd⟩ := hpar v hr (by omega)
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, h2⟩ := ih (par v) (hr.trans hadj.reachable) (by omega)
    exact ⟨h1, by omega⟩
end BondySimonovits
