-- Prove2me | solution 1 for DiazModulus.exists_coordinate_section_add
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:00:51.791756+00:00
-- url     : https://prove2.me/submissions/dae59b97-f4c2-40d8-81eb-782f3033e1a0

import Mathlib

open Complex ComplexConjugate

/-! # A coordinate section of a subspace of `K^{A₀}`

Among the subsets `H ⊆ A₀` on which the projection `π_H : V → K^H` is onto, take one of largest size. Then `π_H` is
also injective: if `v ∈ V ∖ 0` vanished on `H`, pick `a` with `v a ≠ 0` (so `a ∉ H`); any target on `H ∪ {a}` is
reached by `w + t v` with `w` a lift of its restriction to `H` and `t = (x_a − w_a)/v_a`, contradicting maximality.
So `π_H` is a linear bijection `V ≃ K^H` and `dim V = |H|`. Let `e_{h′} ∈ V` (`h′ ∈ H`) be the lift of the
indicator of `h′`; every `v ∈ V` equals `Σ_{h′∈H} v_{h′} e_{h′}` (both lie in `V` and agree on `H`). For `h ∉ H` put
`ℓ_h = X_h − Σ_{h′∈H} (e_{h′})_h X_{h′}` and `ℓ_h = 0` for `h ∈ H`. Then `ℓ_h` vanishes on `V`, and conversely a
vector killed by every `ℓ_h` coincides with the element `Σ_{h′∈H} v_{h′} e_{h′}` of `V`. -/

namespace C13_G4

/-- The projection to `H` is onto. -/
def Onto {K A₀ : Type*} [Field K] (V : Submodule K (A₀ → K)) (H : Finset A₀) : Prop :=
  ∀ x : A₀ → K, ∃ v ∈ V, ∀ h ∈ H, v h = x h

/-- A largest `H` on which the projection is onto. -/
theorem exists_max_onto {K A₀ : Type*} [Field K] [Fintype A₀] (V : Submodule K (A₀ → K)) :
    ∃ H : Finset A₀, Onto V H ∧ ∀ H' : Finset A₀, Onto V H' → H'.card ≤ H.card := by
  classical
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Finset A₀)).filter (fun H => Onto V H)) Finset.card
    ⟨∅, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; intro x; exact ⟨0, V.zero_mem, by simp⟩⟩
  refine ⟨H, (Finset.mem_filter.mp hH).2, fun H' hH' => hmax H' (by simp [hH'])⟩

/-- On a largest onto `H`, the projection is injective. -/
theorem inj_of_max {K A₀ : Type*} [Field K] [Fintype A₀] (V : Submodule K (A₀ → K)) (H : Finset A₀)
    (hH : Onto V H) (hmax : ∀ H' : Finset A₀, Onto V H' → H'.card ≤ H.card) :
    ∀ v ∈ V, (∀ h ∈ H, v h = 0) → v = 0 := by
  classical
  intro v hv hvH
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra h; exact hne (funext fun a => not_not.mp fun h' => h ⟨a, h'⟩)
  have haH : a ∉ H := fun h => ha (hvH a h)
  have hon : Onto V (insert a H) := by
    intro x
    obtain ⟨w, hw, hwx⟩ := hH x
    refine ⟨w + ((x a - w a) / v a) • v, V.add_mem hw (V.smul_mem _ hv), ?_⟩
    intro h hh
    rcases Finset.mem_insert.mp hh with rfl | hh
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; field_simp; ring
    · simp [hwx h hh, hvH h hh]
  have := hmax _ hon
  rw [Finset.card_insert_of_notMem haH] at this
  omega

end C13_G4

open C13_G4 in
theorem solution {K A₀ : Type*} [Field K] [Fintype A₀] (V : Submodule K (A₀ → K)) :
    ∃ (H : Finset A₀) (ℓ : A₀ → A₀ → K), (∀ h ∈ H, ℓ h = 0) ∧ (∀ h ∉ H, ℓ h h = 1 ∧ ∀ h' ∉ H, h' ≠ h → ℓ h h' = 0) ∧
      (∀ v, v ∈ V ↔ ∀ h, ∑ h', ℓ h h' * v h' = 0) ∧ (∀ x : A₀ → K, ∃ v ∈ V, ∀ h ∈ H, v h = x h) ∧
      Module.finrank K ↥V = H.card := by
  classical
  obtain ⟨H, hH, hmax⟩ := exists_max_onto V
  have hinj := inj_of_max V H hH hmax
  -- the lifts of the indicators
  choose e he heH using fun h' : A₀ => hH (fun a => if a = h' then 1 else 0)
  -- every element of `V` is the combination of the lifts given by its coordinates on `H`
  have hcomb : ∀ v : A₀ → K, (∑ h' ∈ H, v h' • e h') ∈ V ∧
      ∀ h ∈ H, (∑ h' ∈ H, v h' • e h') h = v h := by
    intro v
    refine ⟨V.sum_mem fun h' _ => V.smul_mem _ (he h'), fun h hh => ?_⟩
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single h]
    · rw [heH h h hh]; simp
    · intro b _ hb; rw [heH b h hh]; simp [Ne.symm hb]
    · intro h'; exact absurd hh h'
  have hrep : ∀ v ∈ V, ∑ h' ∈ H, v h' • e h' = v := by
    intro v hv
    have := hinj (∑ h' ∈ H, v h' • e h' - v) (V.sub_mem (hcomb v).1 hv)
      (fun h hh => by simp [(hcomb v).2 h hh])
    exact sub_eq_zero.mp this
  refine ⟨H, fun h h' => if h ∈ H then 0 else (if h' = h then 1 else 0) - (if h' ∈ H then e h' h else 0),
    ?_, ?_, ?_, hH, ?_⟩
  · intro h hh; funext h'; simp [hh]
  · intro h hh
    refine ⟨by simp [hh], fun h' hh' hne => by simp [hh, hh', hne]⟩
  · -- the key identity for `h ∉ H`
    have hsum : ∀ v : A₀ → K, ∀ h ∉ H,
        ∑ h', ((if h ∈ H then 0 else (if h' = h then 1 else 0) - (if h' ∈ H then e h' h else 0)) * v h') =
          v h - (∑ h' ∈ H, v h' • e h') h := by
      intro v h hh
      simp only [hh, if_false, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [Finset.sum_apply, ← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Pi.smul_apply, smul_eq_mul, mul_comm]
    intro v
    constructor
    · intro hv h
      by_cases hh : h ∈ H
      · simp [hh]
      · rw [hsum v h hh, hrep v hv, sub_self]
    · intro hv
      have hw := (hcomb v).1
      convert hw using 1
      funext h
      by_cases hh : h ∈ H
      · exact ((hcomb v).2 h hh).symm
      · have := hv h; rw [hsum v h hh] at this; exact (sub_eq_zero.mp this)
  · -- `π_H : V → K^H` is a linear bijection
    let π : ↥V →ₗ[K] (↥H → K) :=
      { toFun := fun v h => (v : A₀ → K) h
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hbij : Function.Bijective π := by
      constructor
      · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro v hv
        have := hinj v v.2 (fun h hh => congrFun hv ⟨h, hh⟩)
        exact Subtype.ext this
      · intro x
        obtain ⟨v, hv, hvx⟩ := hH (fun a => if ha : a ∈ H then x ⟨a, ha⟩ else 0)
        refine ⟨⟨v, hv⟩, funext fun h => ?_⟩
        simp [π, hvx h h.2]
    rw [(LinearEquiv.ofBijective π hbij).finrank_eq, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe]
