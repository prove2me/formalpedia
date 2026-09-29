-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/50644331-4685-5f3f-ab30-496350c01364

import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter.CerednikDrinfeld.Mumford"

namespace CerednikDrinfeld
namespace Mumford
p2m_export "CerednikDrinfeld.Mumford" "vertexType vertexType_apply vertexType_self typePreserving mem_typePreserving_iff GraphAction GraphAction.smul_adj"
namespace VertexTypeLaws
p2m_open "CerednikDrinfeld.Mumford CerednikDrinfeld"

variable {W : Type} {𝒯 : SimpleGraph W}

theorem zmod2_eq_add_one_of_ne : ∀ a b : ZMod 2, a ≠ b → b = a + 1 := by decide

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide

def col (C : 𝒯.Coloring (Fin 2)) (w : W) : ZMod 2 := C w

theorem length_walk_eq_col_sub (C : 𝒯.Coloring (Fin 2)) {u w : W} (p : 𝒯.Walk u w) :
    (p.length : ZMod 2) = col C w - col C u := by
  induction p with
  | nil => rw [SimpleGraph.Walk.length_nil, Nat.cast_zero, sub_self]
  | @cons x y z h p ih =>
      rw [SimpleGraph.Walk.length_cons, Nat.cast_succ, ih]
      have hxy : col C y = col C x + 1 := zmod2_eq_add_one_of_ne _ _ (C.valid h)
      rw [hxy]; ring

theorem vertexType_eq_col_sub (hc : 𝒯.Connected) (C : 𝒯.Coloring (Fin 2)) (w₀ w : W) :
    vertexType 𝒯 w₀ w = col C w - col C w₀ := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist w₀ w
  rw [vertexType_apply, ← hp]
  exact length_walk_eq_col_sub C p

def smulHom (G : Type) [Group G] [MulAction G W] [GraphAction G 𝒯] (g : G) : 𝒯 →g 𝒯 :=
  ⟨fun w => g • w, fun h => GraphAction.smul_adj g h⟩

theorem col_smul_sub (G : Type) [Group G] [MulAction G W] [GraphAction G 𝒯] (hc : 𝒯.Connected)
    (C : 𝒯.Coloring (Fin 2)) (g : G) (w₀ w : W) :
    col C (g • w) - col C (g • w₀) = col C w - col C w₀ := by
  obtain ⟨p, -⟩ := hc.exists_walk_length_eq_dist w₀ w
  have h1 := length_walk_eq_col_sub C p
  have h2 := length_walk_eq_col_sub C (p.map (smulHom G g))
  rw [SimpleGraph.Walk.length_map] at h2
  exact h2.symm.trans h1

theorem main (G : Type) [Group G] [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hc : 𝒯.Connected) (hb : 𝒯.Colorable 2) (w₀ : W) :
    (∀ x y : W, 𝒯.Adj x y → vertexType 𝒯 w₀ y = vertexType 𝒯 w₀ x + 1) ∧
    (∀ (g : G) (w : W), vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ (g • w₀) + vertexType 𝒯 w₀ w) ∧
    (∃ ε : G →* Multiplicative (ZMod 2),
      (∀ g : G, Multiplicative.toAdd (ε g) = vertexType 𝒯 w₀ (g • w₀)) ∧ ε.ker = typePreserving G 𝒯 w₀) := by
  obtain ⟨C⟩ := hb
  have hτ : ∀ w, vertexType 𝒯 w₀ w = col C w - col C w₀ := vertexType_eq_col_sub hc C w₀
  have hb' : ∀ (g : G) (w : W), vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ (g • w₀) + vertexType 𝒯 w₀ w := by
    intro g w
    rw [hτ, hτ, hτ, ← col_smul_sub G hc C g w₀ w]
    ring
  refine ⟨fun x y h => ?_, hb', ?_⟩
  · have hxy : col C y = col C x + 1 := zmod2_eq_add_one_of_ne _ _ (C.valid h)
    rw [hτ, hτ, hxy]; ring
  ·
    let ε : G →* Multiplicative (ZMod 2) :=
      { toFun := fun g => Multiplicative.ofAdd (vertexType 𝒯 w₀ (g • w₀))
        map_one' := by rw [one_smul, vertexType_self]; rfl
        map_mul' := fun g h => by
          rw [← ofAdd_add, mul_smul, hb' g (h • w₀)] }
    refine ⟨ε, fun g => rfl, ?_⟩
    ext g
    rw [MonoidHom.mem_ker, mem_typePreserving_iff]
    constructor
    · intro hg w
      have h0 : vertexType 𝒯 w₀ (g • w₀) = 0 := by
        have := congrArg Multiplicative.toAdd hg
        simp at this
        exact this
      rw [hb', h0, zero_add]
    · intro hg
      have := hg w₀
      rw [vertexType_self] at this
      show Multiplicative.ofAdd (vertexType 𝒯 w₀ (g • w₀)) = 1
      rw [this]; rfl

end CerednikDrinfeld.Mumford.VertexTypeLaws

open CerednikDrinfeld.Mumford.VertexTypeLaws in
theorem solution
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hc : 𝒯.Connected) (hb : 𝒯.Colorable 2) (w₀ : W) :
    (∀ x y : W, 𝒯.Adj x y → vertexType 𝒯 w₀ y = vertexType 𝒯 w₀ x + 1) ∧
    (∀ (g : G) (w : W), vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ (g • w₀) + vertexType 𝒯 w₀ w) ∧
    (∃ ε : G →* Multiplicative (ZMod 2),
      (∀ g : G, Multiplicative.toAdd (ε g) = vertexType 𝒯 w₀ (g • w₀)) ∧ ε.ker = typePreserving G 𝒯 w₀) :=
  main G 𝒯 hc hb w₀

end S_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_vertexType_add_one_of_adj_and_vertexType_smul_and_exists_typeCharacter (solution)
