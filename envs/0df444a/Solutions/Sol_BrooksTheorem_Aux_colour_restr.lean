-- Prove2me | solution 1 for BrooksTheorem.Aux.colour_restr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:39:15.794557+00:00
-- url     : https://prove2.me/submissions/5a0eea4d-262c-4bef-8566-1296e79413fc

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_restr_le
public import Theorems.Thm_BrooksTheorem_Aux_mu_restr_lt
public import Theorems.Thm_BrooksTheorem_Aux_deg_restr

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution {k : ℕ} {H : SimpleGraph V} (ih : IHyp k H) (hdeg : ∀ v, (nb H v).card ≤ k)
    (hcf : H.CliqueFree (k + 1)) (S : Set V) {u v : V} (h : H.Adj u v) (hu : u ∉ S) :
    ∃ f : V → Fin k, Proper (restr H S) f :=
  ih _ (mu_restr_lt H S h hu) (deg_restr hdeg S) (hcf.anti (restr_le H S))
end BrooksTheorem.Aux
