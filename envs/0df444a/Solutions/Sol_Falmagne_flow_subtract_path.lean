-- Prove2me | solution 1 for Falmagne.flow_subtract_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:39.538201+00:00
-- url     : https://prove2.me/submissions/ebc33b04-add4-4c99-8156-b1ba9255682e

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Flow
public import Theorems.Thm_Falmagne_exists_positive_path
public import Theorems.Thm_Falmagne_mem_edgeSupport
public import Theorems.Thm_Falmagne_inflow_mul
public import Theorems.Thm_Falmagne_inflow_sub
public import Theorems.Thm_Falmagne_outflow_mul
public import Theorems.Thm_Falmagne_outflow_sub
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_pathFlow_conserve
public import Theorems.Thm_Falmagne_pathFlow_eq_zero_or_one
public import Theorems.Thm_Falmagne_pathFlow_head
public import Theorems.Thm_Falmagne_pathFlow_nil
public import Theorems.Thm_Falmagne_pathFlow_nonneg
public import Theorems.Thm_Falmagne_pathFlow_nonzero_mem
public import Theorems.Thm_Falmagne_pathFlow_source
attribute [local simp] Falmagne.pathFlow_cons
attribute [local simp] Falmagne.pathFlow_nil


attribute [local simp] Falmagne.mem_edgeSupport

set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}
namespace Falmagne
theorem _root_.solution [Nonempty X] (h : IsFlow q m) (hm : 0 < m) :
    ∃ (l : List X) (δ : ℝ), l.Nodup ∧ l.toFinset = Finset.univ ∧ 0 < δ ∧
      IsFlow (fun x A => q x A - δ * pathFlow l x A) (m - δ) ∧
      (edgeSupport (fun x A => q x A - δ * pathFlow l x A)).card < (edgeSupport q).card := by
  classical
  obtain ⟨l, hln, hfull, hpos⟩ := exists_positive_path h Finset.univ (by rw [h.source]; exact hm)
  let E : Finset (X × Finset X) := Finset.univ.filter fun e => pathFlow l e.1 e.2 ≠ 0
  have hEmem : ∀ e, e ∈ E ↔ pathFlow l e.1 e.2 ≠ 0 := by intro e; simp [E]
  have hEn : E.Nonempty := by
    cases l with
    | nil =>
        have hu : (Finset.univ : Finset X) = ∅ := hfull.symm
        exact (Finset.univ_nonempty.ne_empty hu).elim
    | cons y l =>
        refine ⟨(y, (y :: l).toFinset), ?_⟩
        rw [hEmem]
        rw [pathFlow_head y l (List.nodup_cons.mp hln).1]
        norm_num
  obtain ⟨e, he, hmin⟩ := Finset.exists_min_image E (fun e => q e.1 e.2) hEn
  let δ := q e.1 e.2
  have hδ : 0 < δ := hpos e.1 e.2 ((hEmem e).mp he)
  have hpe : pathFlow l e.1 e.2 = 1 :=
    (pathFlow_eq_zero_or_one l hln e.1 e.2).resolve_left ((hEmem e).mp he)
  have hnn : ∀ x A, x ∈ A → 0 ≤ q x A - δ * pathFlow l x A := by
    intro x A hx
    rcases pathFlow_eq_zero_or_one l hln x A with hp | hp
    · simpa [hp] using h.nonneg x A hx
    · have hE : (x, A) ∈ E := (hEmem _).mpr (by rw [hp]; norm_num)
      have hle := hmin (x, A) hE
      simpa [hp, δ] using sub_nonneg.mpr hle
  have hr : IsFlow (fun x A => q x A - δ * pathFlow l x A) (m - δ) := by
    refine ⟨hnn, ?_, ?_⟩
    · rw [outflow_sub, outflow_mul, h.source, pathFlow_source l hln hfull, mul_one]
    · intro A hA hU
      rw [outflow_sub, inflow_sub, outflow_mul, inflow_mul, h.conserve A hA hU,
        pathFlow_conserve l hln hfull A hA hU]
  refine ⟨l, δ, hln, hfull, hδ, hr, ?_⟩
  apply Finset.card_lt_card
  have hsub : edgeSupport (fun x A => q x A - δ * pathFlow l x A) ⊆ edgeSupport q := by
    intro z hz
    obtain ⟨hzm, hzpos⟩ := (mem_edgeSupport _ z).mp hz
    apply (mem_edgeSupport _ z).mpr
    refine ⟨hzm, ?_⟩
    have hpnn := pathFlow_nonneg l z.1 z.2
    have hδnn : 0 ≤ δ := le_of_lt hδ
    nlinarith
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  have heqmem : e ∈ edgeSupport q := (mem_edgeSupport _ e).mpr
    ⟨pathFlow_nonzero_mem l ((hEmem e).mp he), hδ⟩
  rw [← heq] at heqmem
  have hfalse := ((mem_edgeSupport _ e).mp heqmem).2
  simp [δ, hpe] at hfalse
end Falmagne
