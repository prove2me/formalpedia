-- Prove2me | solution 1 for CompactnessConjecture.badFourPathTripleToBadIndependentTriple_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/81b9be28-d961-4681-bed9-80a1914f1f03

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_fourPathTripleToIndependentThetaTriple_endpoint_mem
import Theorems.Thm_CompactnessConjecture_badIndependentThetaTriple_other_center_unique

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G) :
    Function.Injective
      (badFourPathTripleToBadIndependentTriple
        G hbip hfour hsix) := by
  rintro ⟨u, v, base⟩ ⟨u', v', base'⟩ heq
  have hcenter := congrArg
    (fun witness : BadIndependentTripleWitness G =>
      (witness.2 : V)) heq
  change (u : V) = (u' : V) at hcenter
  have husub : u = u' := Subtype.ext hcenter
  subst u'
  have hbase := congrArg
    (fun witness : BadIndependentTripleWitness G =>
      witness.1.val) heq
  change base.val = base'.val at hbase
  let triple := fourPathTripleToIndependentThetaTriple
    G hbip hfour hsix (u : V) v base
  have hu : (u : V) ∈ commonCenterFinset G triple.val :=
    fourPathTripleToIndependentThetaTriple_center_mem
      G hbip hfour hsix (u : V) v base
  have hv : (v : V) ∈ commonCenterFinset G triple.val :=
    fourPathTripleToIndependentThetaTriple_endpoint_mem
      G hbip hfour hsix (u : V) v base
  have hv' : (v' : V) ∈ commonCenterFinset G triple.val := by
    change (v' : V) ∈ commonCenterFinset G base.val
    rw [hbase]
    exact fourPathTripleToIndependentThetaTriple_endpoint_mem
      G hbip hfour hsix (u : V) v' base'
  have hendpoint : (v : V) = (v' : V) :=
    badIndependentThetaTriple_other_center_unique
      G hbip hfour hsix triple (u : V) hu u.property hv hv'
      v.property.1 v'.property.1
  have hvsub : v = v' := Subtype.ext hendpoint
  subst v'
  have hbasesub : base = base' := Subtype.ext hbase
  subst base'
  rfl
end CompactnessConjecture
