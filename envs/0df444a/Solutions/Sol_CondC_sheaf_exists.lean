-- Prove2me | solution 1 for CondC.sheaf_exists
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:50:31.865433+00:00
-- url     : https://prove2.me/submissions/c3c9d214-b2b7-47eb-acfd-e92cd61aa54f

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

theorem solution : ¬ (∃ (P : DiscModulePresheaf) (O : OIdentification P),
    SheafGlue2 P ∧
    ∀ (Q : DiscModulePresheaf) (O' : OIdentification Q), SheafGlue2 Q →
      ∃! e : (d : Disc) → P.F d ≃ Q.F d,
        (∀ (d d' : Disc) (h : SubDisc d d') (s : P.F d'),
          Q.res d d' h (e d' s) = e d (P.res d d' h s)) ∧
        (∀ (d : Disc) (s : P.F d), O.coeffs d s = O'.coeffs d (e d s))) := by
  rintro ⟨P, O, -, hU⟩
  let d₂ : Disc := (0, 1)
  let d₁ : Disc := (0, 1 / 2)
  have hsub : SubDisc d₁ d₂ := by simp only [SubDisc, d₁, d₂, dist_self]; norm_num
  have hne : d₂ ≠ d₁ := by intro h; have := congrArg Prod.snd h; simp [d₁, d₂] at this
  let τ₂ : Disc → (ℕ → ℂ) ≃ (ℕ → ℂ) := fun d => if d = d₁ then Equiv.neg _ else Equiv.refl _
  obtain ⟨e₁, ⟨hr₁, hc₁⟩, -⟩ := hU g72sh_Q (g72sh_O fun _ => Equiv.refl _) g72sh_glue
  obtain ⟨e₂, ⟨hr₂, hc₂⟩, -⟩ := hU g72sh_Q (g72sh_O τ₂) g72sh_glue
  have key : ∀ s : P.F d₂, (e₁ d₂ s : ℕ → ℂ) = 0 := by
    intro s
    -- equality at d₂
    have a := (hc₁ d₂ s).symm.trans (hc₂ d₂ s)
    simp only [g72sh_O, τ₂, if_neg hne] at a
    have a' : (e₁ d₂ s : ℕ → ℂ) = e₂ d₂ s := (g72sh_psi _).injective (Subtype.ext a)
    -- equality at d₁
    set t := P.res d₁ d₂ hsub s
    have b := (hc₁ d₁ t).symm.trans (hc₂ d₁ t)
    simp only [g72sh_O, τ₂, ite_true] at b
    have b' : (e₁ d₁ t : ℕ → ℂ) = -(e₂ d₁ t : ℕ → ℂ) := (g72sh_psi _).injective (Subtype.ext b)
    have r1 : (e₁ d₂ s : ℕ → ℂ) = e₁ d₁ t := hr₁ d₁ d₂ hsub s
    have r2 : (e₂ d₂ s : ℕ → ℂ) = e₂ d₁ t := hr₂ d₁ d₂ hsub s
    have : (e₁ d₂ s : ℕ → ℂ) = -(e₁ d₂ s) := by
      calc (e₁ d₂ s : ℕ → ℂ) = e₁ d₁ t := r1
        _ = -(e₂ d₁ t : ℕ → ℂ) := b'
        _ = -(e₂ d₂ s : ℕ → ℂ) := by rw [r2]
        _ = -(e₁ d₂ s : ℕ → ℂ) := by rw [a']
    have h2 : (2 : ℂ) • (e₁ d₂ s : ℕ → ℂ) = 0 := by
      rw [two_smul]; nth_rewrite 1 [this]; exact neg_add_cancel _
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  obtain ⟨s, hs⟩ := (e₁ d₂).surjective (fun _ => 1)
  have := key s
  rw [hs] at this
  exact one_ne_zero (congrFun this 0 : (1 : ℂ) = 0)
