-- Prove2me | solution 1 for CriticalPortraits.spanning_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:36:58.288844+00:00
-- url     : https://prove2.me/submissions/571ba5ad-154e-43f1-a935-ab77238e079d

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Theorems.Thm_AbstractLaminar_covered_of_ne_gap
public import Theorems.Thm_CriticalPortraits_edge_tight_geom
public import Theorems.Thm_CriticalPortraits_column_sep_geom
public import Theorems.Thm_CriticalPortraits_column_sep_geom_dir
public import Theorems.Thm_CriticalPortraits_root_val_lt
public import Theorems.Thm_AbstractLaminar_root_self_props
public import Theorems.Thm_CriticalPortraits_sep_master


set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}
namespace CriticalPortraits
theorem _root_.solution [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) {x : ZMod (d * m)} (hx : x ∈ T P)
    {ℓ : ℕ} (hℓ1 : loV P x < ℓ) (hℓ2 : ℓ < hiV x) :
    ∃ b, ∃ hb : b ∈ T P, colV b ≠ colV x ∧
      (predIn P b hb).val < colV x + ℓ * m ∧ colV x + ℓ * m < b.val ∧ b.val < x.val := by
  set fam := survivorFamily hd hm hP with hfam
  have hwin : loV P x < hiV x := by change fam.lo x < fam.hi x; exact fam.lh x hx
  have hsat : AbstractLaminar.N fam (loV P x) (hiV x) = hiV x - loV P x :=
    edge_tight_geom hd hm hP hx
  have htop : (AbstractLaminar.topEdges fam (loV P x) (hiV x)).Nonempty := by
    refine ⟨x, ?_⟩
    unfold AbstractLaminar.topEdges
    rw [Finset.mem_filter, AbstractLaminar.mem_contained]
    exact ⟨⟨hx, le_refl _, le_refl _⟩, rfl, rfl⟩
  have hcx := colV_lt_m hm x
  -- gap + directional column facts.
  obtain ⟨gp, hgp1, hgp2, hgpgap, hleft, hright⟩ := column_sep_geom_dir hd hm hP hx hwin
  -- a generic finisher: given a root r covering value v₀ = colV x + ℓ*m in its arc, finish.
  -- We split on ℓ < gp (use the tile covering ℓ) vs ℓ ≥ gp (use the tile covering ℓ+1).
  rcases Nat.lt_or_ge ℓ gp with hlg | hge
  · -- ℓ < gp : the root covering level ℓ straddles v₀.
    obtain ⟨r, hr, hrlo0, hrhi0⟩ :=
      AbstractLaminar.covered_of_ne_gap fam htop hsat hwin hgp1 hgp2 hgpgap
        (show loV P x < ℓ from hℓ1) (le_of_lt hℓ2) (by omega : ℓ ≠ gp)
    have hrlo : loV P r < ℓ := hrlo0
    have hrhi : ℓ ≤ hiV r := hrhi0
    obtain ⟨hrE, hra0, hrb0, _⟩ := AbstractLaminar.root_self_props fam hr
    have hra : loV P x ≤ loV P r := hra0
    have hrb : hiV r ≤ hiV x := hrb0
    have hcolne : colV r ≠ colV x := column_sep_geom hd hm hP hx hwin r hr
    have hgpgap' : ¬ (loV P r < gp ∧ gp ≤ hiV r) := hgpgap r hr
    have hrhig : hiV r < gp := by
      by_contra hc; push Not at hc; exact hgpgap' ⟨by omega, hc⟩
    have hcolxr : colV x < colV r := hleft r hr hrhig
    have hcr := colV_lt_m hm r
    have hpr : (predIn P r hrE).val = colV r + loV P r * m := pred_val_eq hP hrE
    have hrv : r.val = colV r + hiV r * m := top_val_eq (x := r)
    refine ⟨r, hrE, hcolne, ?_, ?_, ?_⟩
    · have := sep_master (m := m) (p := colV r) (q := colV x) hcr hcx hrlo
      rw [hpr]; omega
    · rcases lt_or_eq_of_le hrhi with hlt | heq
      · have := sep_master (m := m) (p := colV x) (q := colV r) hcx hcr hlt
        rw [hrv]; omega
      · rw [hrv, ← heq]; omega
    · exact root_val_lt hd hm hP hrE hx hra hrb hcolne
  · -- ℓ ≥ gp : the root covering level ℓ+1 straddles v₀.
    have hℓ1' : loV P x < ℓ + 1 := by omega
    have hℓ2' : ℓ + 1 ≤ hiV x := by omega
    have hne' : ℓ + 1 ≠ gp := by omega
    obtain ⟨r, hr, hrlo0, hrhi0⟩ :=
      AbstractLaminar.covered_of_ne_gap fam htop hsat hwin hgp1 hgp2 hgpgap hℓ1' hℓ2' hne'
    have hrlo : loV P r < ℓ + 1 := hrlo0
    have hrhi : ℓ + 1 ≤ hiV r := hrhi0
    obtain ⟨hrE, hra0, hrb0, _⟩ := AbstractLaminar.root_self_props fam hr
    have hra : loV P x ≤ loV P r := hra0
    have hrb : hiV r ≤ hiV x := hrb0
    have hcolne : colV r ≠ colV x := column_sep_geom hd hm hP hx hwin r hr
    have hrlo' : loV P r ≤ ℓ := by omega
    have hgpgap' : ¬ (loV P r < gp ∧ gp ≤ hiV r) := hgpgap r hr
    have hgr : gp ≤ loV P r := by
      by_contra hc; push Not at hc; exact hgpgap' ⟨hc, by omega⟩
    have hcolrx : colV r < colV x := hright r hr hgr
    have hcr := colV_lt_m hm r
    have hpr : (predIn P r hrE).val = colV r + loV P r * m := pred_val_eq hP hrE
    have hrv : r.val = colV r + hiV r * m := top_val_eq (x := r)
    refine ⟨r, hrE, hcolne, ?_, ?_, ?_⟩
    · rcases lt_or_eq_of_le hrlo' with hlt | heq
      · have := sep_master (m := m) (p := colV r) (q := colV x) hcr hcx hlt
        rw [hpr]; omega
      · rw [hpr, heq]; omega
    · have := sep_master (m := m) (p := colV x) (q := colV r) hcx hcr (show ℓ < hiV r by omega)
      rw [hrv]; omega
    · exact root_val_lt hd hm hP hrE hx hra hrb hcolne
end CriticalPortraits
