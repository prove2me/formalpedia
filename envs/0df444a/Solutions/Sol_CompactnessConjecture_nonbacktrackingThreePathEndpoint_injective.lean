-- Prove2me | solution 1 for CompactnessConjecture.nonbacktrackingThreePathEndpoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/f5b1e399-67f0-4f16-a17f-f8914a06a42d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace CompactnessConjecture
theorem _root_.solution
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    {u : V} :
    Function.Injective
      (nonbacktrackingThreePathEndpoint G (u := u)) := by
  rintro ⟨a, w, b⟩ ⟨a', w', b'⟩ hb
  change (b : V) = (b' : V) at hb
  have haa : (a : V) = (a' : V) := by
    by_contra hne
    have hww : (w : V) ≠ (w' : V) := by
      intro heq
      have hwa' : G.Adj (w : V) (a' : V) :=
        Eq.mp
          (congrArg (fun x : V => G.Adj x (a' : V)) heq.symm)
          w'.property.1.symm
      have heqa : (a : V) = (a' : V) :=
        common_neighbor_unique_of_four_cycle_free hfour
          w.property.2.symm
          a.property w.property.1.symm
          a'.property hwa'
      exact hne heqa
    have hwb : G.Adj (w' : V) (b : V) :=
      Eq.mp (congrArg (G.Adj (w' : V)) hb.symm)
        b'.property.1
    have htriangle := common_neighbors_triangle_eq_of_cycle_free
      hbip hfour hsix
      w.property.2.symm hww w'.property.2.symm
      a.property w.property.1.symm
      b.property.1 hwb
      w'.property.1.symm a'.property
    exact b.property.2 htriangle.1.symm
  have ha : a = a' := Subtype.ext haa
  subst a'
  have hwb' : G.Adj (b : V) (w' : V) :=
    Eq.mp (congrArg (fun x : V => G.Adj x (w' : V)) hb.symm)
      b'.property.1.symm
  have hww : (w : V) = (w' : V) :=
    common_neighbor_unique_of_four_cycle_free hfour
      b.property.2.symm
      w.property.1 b.property.1.symm
      w'.property.1 hwb'
  have hw : w = w' := Subtype.ext hww
  subst w'
  have hb' : b = b' := Subtype.ext hb
  subst b'
  rfl
end CompactnessConjecture
