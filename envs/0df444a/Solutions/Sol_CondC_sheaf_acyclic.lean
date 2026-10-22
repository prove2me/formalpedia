-- Prove2me | solution 1 for CondC.sheaf_acyclic
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:50:30.789578+00:00
-- url     : https://prove2.me/submissions/a1fed0f8-8b3b-4138-bf5d-10d81f3818db

import Mathlib
import Definitions.Def_CondC_liq
import Definitions.Def_CondC_geo

open CondC

section g72sh

theorem g72sh_single (r : ℝ) (c : ℂ) : PowerDecay r (fun n => if n = 0 then c else 0) := by
  intro r' _ _
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have : n ≠ 0 := by omega
  simp [this]

theorem g72sh_card (r : ℝ) : Cardinal.mk {f : ℕ → ℂ // PowerDecay r f} = Cardinal.mk (ℕ → ℂ) := by
  apply le_antisymm (Cardinal.mk_subtype_le _)
  have h1 : Cardinal.mk (ℕ → ℂ) = Cardinal.continuum := by
    rw [← Cardinal.power_def, Cardinal.mk_complex, Cardinal.mk_nat, Cardinal.continuum_power_aleph0]
  rw [h1, ← Cardinal.mk_complex]
  refine Cardinal.mk_le_of_injective (f := fun c => (⟨fun n => if n = 0 then c else 0, g72sh_single r c⟩ :
    {f : ℕ → ℂ // PowerDecay r f})) ?_
  intro a b h
  have := congrArg (fun x => x.1 0) h
  simpa using this

noncomputable def g72sh_psi (r : ℝ) : (ℕ → ℂ) ≃ {f : ℕ → ℂ // PowerDecay r f} :=
  (Classical.choice (Cardinal.eq.1 (g72sh_card r))).symm

abbrev g72sh_Q : DiscModulePresheaf where
  F := fun _ => ℕ → ℂ
  res := fun _ _ _ s => s
  res_refl := fun _ _ => rfl
  res_trans := fun _ _ _ _ _ _ => rfl
  add := fun _ _ _ => 0
  zero := fun _ => 0
  neg := fun _ s => s
  smul := fun _ _ s => s
  add_res := fun _ _ _ _ _ => rfl
  zero_res := fun _ _ _ => rfl
  neg_res := fun _ _ _ _ => rfl
  smul_res := fun _ _ _ _ _ => rfl

noncomputable def g72sh_O (τ : Disc → (ℕ → ℂ) ≃ (ℕ → ℂ)) : OIdentification g72sh_Q where
  coeffs := fun d s => (g72sh_psi d.2 (τ d s)).1
  decay := fun d s _ => (g72sh_psi d.2 (τ d s)).2
  inj := fun d s t h => by
    have := Subtype.ext h
    exact (τ d).injective ((g72sh_psi d.2).injective this)
  surj := fun d _ f hf => ⟨(τ d).symm ((g72sh_psi d.2).symm ⟨f, hf⟩), by simp⟩

theorem g72sh_glue : SheafGlue2 g72sh_Q := by
  intro d c s₀ s₁ hag
  let e : Disc := (0, -(‖c.d₀.1‖ + ‖c.d₁.1‖ + |c.d₀.2| + |c.d₁.2|))
  have h0 : SubDisc e c.d₀ := by
    simp only [SubDisc, e, dist_zero_left]
    have := neg_abs_le c.d₀.2; have := norm_nonneg c.d₁.1; have := abs_nonneg c.d₁.2; linarith
  have h1 : SubDisc e c.d₁ := by
    simp only [SubDisc, e, dist_zero_left]
    have := neg_abs_le c.d₁.2; have := norm_nonneg c.d₀.1; have := abs_nonneg c.d₀.2; linarith
  have hs : s₀ = s₁ := hag e h0 h1
  refine ⟨s₀, ⟨rfl, hs⟩, fun s hs' => hs'.1⟩

end g72sh

theorem solution : ¬ (∀ (P : DiscModulePresheaf) (_ : OIdentification P),
    SheafGlue2 P → H1Vanishes P) := by
  intro h
  have H := h g72sh_Q (g72sh_O fun _ => Equiv.refl _) g72sh_glue
  let d : Disc := (0, 1)
  let c : Covers2 d := ⟨d, d, subDisc_refl d, subDisc_refl d, fun z hz => Or.inl hz⟩
  obtain ⟨s, hs0, hs1⟩ := H d c (0 : ℕ → ℂ) (fun _ => 1) (fun _ _ _ => rfl)
  have : (0 : ℕ → ℂ) = fun _ => 1 := hs0.symm.trans hs1
  have := congrFun this 0
  simp at this
