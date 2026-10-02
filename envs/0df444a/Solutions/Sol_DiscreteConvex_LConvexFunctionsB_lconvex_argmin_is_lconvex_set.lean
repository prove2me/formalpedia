-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsB.lconvex_argmin_is_lconvex_set
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T04:12:36.568025+00:00
-- url     : https://prove2.me/submissions/4f6987a5-980e-4a53-bb58-a702a29108f2

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_ArgMin
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_SBF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_TRF
import Definitions.Def_DiscreteConvex_LConvexFunctionsB_LConvexSet

set_option autoImplicit false

namespace DiscreteConvex.LConvexFunctionsB

theorem p341_key (m c d : WithTop ℝ) (hc : m ≤ c) (hd : m ≤ d) (h : m + m ≥ c + d) :
    c ≤ m ∧ d ≤ m := by
  induction m using WithTop.recTopCoe with
  | top =>
    rw [top_le_iff] at hc hd
    subst hc; subst hd
    exact ⟨le_rfl, le_rfl⟩
  | coe a =>
    have hcd : c + d ≠ ⊤ := by
      intro hh; rw [hh] at h
      exact (WithTop.coe_ne_top (a := a + a)) (by rw [WithTop.coe_add]; exact top_le_iff.mp h)
    have hc' : c ≠ ⊤ := fun hh => hcd (by rw [hh, WithTop.top_add])
    have hd' : d ≠ ⊤ := fun hh => hcd (by rw [hh, WithTop.add_top])
    lift c to ℝ using hc'
    lift d to ℝ using hd'
    rw [ge_iff_le, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h
    rw [WithTop.coe_le_coe] at hc hd ⊢
    rw [WithTop.coe_le_coe]
    constructor <;> linarith

end DiscreteConvex.LConvexFunctionsB

open DiscreteConvex.LConvexFunctionsB Classical in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (g : (V → ℤ) → WithTop ℝ) (hg : SBF g ∧ TRF g)
    (hne : (ArgMin g).Nonempty) : LConvexSet (ArgMin g) := by
  refine ⟨hne, ?_, ?_⟩
  · intro p hp q hq
    have hp' : ∀ x, g p ≤ g x := hp
    have hq' : ∀ x, g q ≤ g x := hq
    have hpq : g p = g q := le_antisymm (hp' q) (hq' p)
    have h := hg.1 p q
    rw [← hpq] at h
    have k := p341_key (g p) (g (p ⊔ q)) (g (p ⊓ q)) (hp' _) (hp' _) h
    exact ⟨fun x => le_trans k.1 (hp' x), fun x => le_trans k.2 (hp' x)⟩
  · intro p hp
    have hp' : ∀ x, g p ≤ g x := hp
    obtain ⟨r, hr⟩ := hg.2
    have h1 : g (p + 1) = g p + (r : WithTop ℝ) := hr p
    have h2 : g p = g (p - 1) + (r : WithTop ℝ) := by
      have := hr (p - 1); rwa [sub_add_cancel] at this
    have e1 : (fun v => p v + 1) = p + 1 := rfl
    have e2 : (fun v => p v - 1) = p - 1 := rfl
    rw [e1, e2]
    induction hgp : g p using WithTop.recTopCoe with
    | top =>
      have hall : ∀ x, g x = ⊤ := fun x => top_le_iff.mp (hgp ▸ hp' x)
      exact ⟨fun x => by rw [hall x]; exact le_top, fun x => by rw [hall x]; exact le_top⟩
    | coe a =>
      have hm1 : g (p - 1) ≠ ⊤ := by
        intro hh; rw [hh, WithTop.top_add, hgp] at h2; exact WithTop.coe_ne_top h2
      have hlo := hp' (p - 1)
      have hhi := hp' (p + 1)
      rw [hgp] at hlo hhi h2 h1
      lift g (p - 1) to ℝ using hm1 with b hb
      rw [← WithTop.coe_add, WithTop.coe_inj] at h2
      rw [h1, ← WithTop.coe_add, WithTop.coe_le_coe] at hhi
      rw [WithTop.coe_le_coe] at hlo
      have hr0 : r = 0 := by linarith
      refine ⟨fun x => ?_, fun x => ?_⟩
      · have := hp' x; rw [hgp] at this; rw [h1, ← WithTop.coe_add, hr0, add_zero]; exact this
      · have := hp' x; rw [hgp] at this; rw [← hb]
        have hba : b = a := by linarith
        rw [hba]; exact this
