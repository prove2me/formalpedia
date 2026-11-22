-- Prove2me | solution 1 for DeciSigma1.Arithmetic.DifferenceSystem.least_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:13.187149+00:00
-- url     : https://prove2.me/submissions/8d7e52eb-2091-4593-8b5d-6607658c0f2f

module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
open DeciSigma1.Arithmetic.DifferenceSystem
variable {ι : Type} (D : DifferenceSystem ι)
variable {D}
open Classical
namespace DeciSigma1.Arithmetic.DifferenceSystem
theorem _root_.solution (floor x0 : ι → ℤ) (h0 : D.Sat x0) (hf : floor ≤ x0) :
    ∃ xm, D.Sat xm ∧ floor ≤ xm ∧ (∀ x, D.Sat x → floor ≤ x → xm ≤ x) ∧
      ∀ i, ∃ p : List ι, p.Nodup ∧ p.getLast? = some i ∧
        (∃ j, p.head? = some j ∧ xm j = floor j) ∧ p.IsChain (D.IsTight xm) := by
  have hex : ∀ i, ∃ n : ℕ, ∃ x, D.Sat x ∧ floor ≤ x ∧ x i = floor i + n := by
    intro i
    have hfi : floor i ≤ x0 i := hf i
    exact ⟨(x0 i - floor i).toNat, x0, h0, hf, by omega⟩
  let xm : ι → ℤ := fun i => floor i + Nat.find (hex i)
  have hmin : ∀ x, D.Sat x → floor ≤ x → xm ≤ x := by
    intro x hx hfx i
    have hfi : floor i ≤ x i := hfx i
    have := Nat.find_min' (hex i) ⟨x, hx, hfx, (by omega :
      x i = floor i + (x i - floor i).toNat)⟩
    simp only [xm]
    omega
  have hsat : D.Sat xm := by
    intro i j c hc
    obtain ⟨y, hy, hfy, hyj⟩ := Nat.find_spec (hex j)
    have h1 := hmin y hy hfy i
    have h2 := hy i j c hc
    simp only [xm] at h1 ⊢
    linarith
  have hfm : floor ≤ xm := fun i => by simp only [xm]; omega
  refine ⟨xm, hsat, hfm, hmin, fun i => ?_⟩
  -- the vertices with a duplicate-free tight path to `i`
  let R : ι → Prop := fun j => ∃ p : List ι, p.Nodup ∧ p.getLast? = some i ∧ p.head? = some j ∧
    p.IsChain (D.IsTight xm)
  have hRi : R i := ⟨[i], List.nodup_singleton i, rfl, rfl, List.isChain_singleton i⟩
  have hRclosed : ∀ u v, D.IsTight xm u v → R v → R u := by
    rintro u v huv ⟨p, hnd, hlast, hhead, hch⟩
    obtain ⟨p', rfl⟩ : ∃ p', p = v :: p' := by
      cases p with
      | nil => simp at hhead
      | cons a p' => simp only [List.head?_cons, Option.some_inj] at hhead; exact ⟨p', hhead ▸ rfl⟩
    by_cases hu : u ∈ v :: p'
    · obtain ⟨s, t, hst⟩ := List.append_of_mem hu
      refine ⟨u :: t, ?_, ?_, rfl, ?_⟩
      · rw [hst] at hnd; exact hnd.sublist (List.sublist_append_right _ _)
      · rw [hst] at hlast; rw [← hlast, List.getLast?_append_cons]
      · rw [hst] at hch; exact (List.isChain_split.mp hch).2
    · refine ⟨u :: v :: p', List.nodup_cons.mpr ⟨hu, hnd⟩, ?_, rfl, ?_⟩
      · rw [List.getLast?_cons_cons]; exact hlast
      · exact List.isChain_cons_cons.mpr ⟨huv, hch⟩
  by_contra hno
  have hnoR : ∀ j, R j → floor j < xm j := by
    intro j ⟨p, hnd, hlast, hhead, hch⟩
    rcases lt_or_eq_of_le (hfm j) with h | h
    · exact h
    · exact absurd ⟨p, hnd, hlast, ⟨j, hhead, h.symm⟩, hch⟩ hno
  -- lowering every vertex of `R` by one keeps a solution above the floors
  let x' : ι → ℤ := fun v => if R v then xm v - 1 else xm v
  have hsat' : D.Sat x' := by
    intro u v c hc
    have huv := hsat u v c hc
    by_cases hv : R v
    · by_cases hu : R u
      · simp only [x', hu, hv, ite_true]; linarith
      · have hnt : xm u + c ≠ xm v := fun he => hu (hRclosed u v ⟨c, hc, he⟩ hv)
        simp only [x', hu, hv, ite_true, ite_false]; omega
    · by_cases hu : R u
      · simp only [x', hu, hv, ite_true, ite_false]; linarith
      · simp only [x', hu, hv, ite_false]; exact huv
  have hf' : floor ≤ x' := by
    intro v
    by_cases hv : R v
    · simp only [x', hv, ite_true]; have := hnoR v hv; omega
    · simp only [x', hv, ite_false]; exact hfm v
  have := hmin x' hsat' hf' i
  simp only [x', hRi, ite_true] at this
  omega
end DeciSigma1.Arithmetic.DifferenceSystem
