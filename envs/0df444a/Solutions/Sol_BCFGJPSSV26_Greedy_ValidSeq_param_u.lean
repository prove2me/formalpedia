-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.ValidSeq.param_u
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:58:36.19464+00:00
-- url     : https://prove2.me/submissions/3045f8a6-f08f-4030-8710-125242af421c

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Openable
public import Definitions.Def_BCFGJPSSV26_Greedy_Valid
import all Definitions.Def_BCFGJPSSV26_Greedy_Valid
public import Theorems.Thm_BCFGJPSSV26_Greedy_maximal_transfer

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

variable {P d}

/-- **Changing one offset** ([BCFGJPSSV26a, Claim D.12], second case): a sequence that is
`0`-valid after `A ++ (z, u') :: B` is `η`-valid after `A ++ (z, u) :: B` for
`u ∈ [u' - η, u']`, without overbidding after the former. -/
theorem ValidSeq.param_u (hP : P.Good n) (hd0 : ∀ j i, 0 ≤ d j i) {f η : ℚ} {p : ℕ}
    {A B H : List (Atom m)} {z : Fin m} {u u' : ℚ} (hu0 : 0 ≤ u) (hu : u ≤ u')
    (hu' : u' - η ≤ u) (h0 : ValidSeq P d f 0 p (A ++ ⟨z, u', true⟩ :: B) H)
    (hno : NoOver P d f (P.θseq p) (profL P.K d (A ++ ⟨z, u', true⟩ :: B))) :
    ValidSeq P d f η p (A ++ ⟨z, u, true⟩ :: B) H := by
  have hη : 0 ≤ η := by linarith
  have hmid : ∀ (v : ℚ) (C : List (Atom m)), pairs (A ++ ⟨z, v, true⟩ :: B ++ C) =
      insert (z, v) (pairs (A ++ B ++ C)) := fun v C ↦ by
    rw [List.append_assoc, List.cons_append, pairs_cons_mid, List.append_assoc]
    rfl
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · rcases h0.1 t ht with hfree | ⟨S, hS, hS0, hS'⟩
    · exact .inl hfree
    · -- the witness: the superset with `(z, u)` added
      rw [hmid] at hS
      have hzu' : (z, u') ∈ S := hS (mem_insert_self _ _)
      refine .inr ⟨insert (z, u) S, ?_, ?_, ?_⟩
      · rw [hmid]
        exact insert_subset_insert _ ((subset_insert _ _).trans hS)
      · intro q hq
        rw [mem_insert] at hq
        rcases hq with rfl | hq
        · exact hu0
        · exact hS0 q hq
      · have hD : ∀ j, profF P.K d S j - η ≤ profF P.K d (insert (z, u) S) j := fun j ↦ by
          rw [profF_insert]
          have := profF_le P.K d hzu' j
          exact le_min (by simp only at this ⊢; linarith) (by linarith)
        have hD' : profF P.K d (insert (z, u) S) ≤ profF P.K d S :=
          fun j ↦ profF_anti _ _ (subset_insert _ _) j
        cases hb : typ1 p <;> simp only [OpenT, hb, cond] at hS' ⊢
        · obtain ⟨T, h1, h2, h3, h4⟩ := hS'
          rw [mul_zero, sub_zero] at h3
          refine ⟨T, h1, h2, ?_, fun i₀ ↦ (lhs4_mono_D hP hD').trans (h4 i₀)⟩
          have := lhs3_sub_le hP hη hD (θ := P.θseq p) (i := (H[t]).fac) (T := T) (d := d)
          linarith
        · unfold Open1 at hS' ⊢
          rw [mul_zero, sub_zero] at hS'
          have := lhs1_sub_le hP hη hD (θ := P.θseq p) (i := (H[t]).fac) (d := d)
          linarith
  · have hle : profL P.K d (A ++ ⟨z, u, true⟩ :: B ++ H) ≤
        profL P.K d (A ++ ⟨z, u', true⟩ :: B ++ H) := fun j ↦ by
      unfold profL
      rw [hmid, hmid, profF_insert, profF_insert]
      exact min_le_min (by simp only; linarith) le_rfl
    have hno' : NoOver P d f (P.θseq p) (profL P.K d (A ++ ⟨z, u', true⟩ :: B ++ H)) :=
      hno.mono hP fun j ↦ profL_anti _ _ (pairs_mono (List.subset_append_left _ _)) j
    exact maximal_transfer hP hd0 (typ1 p) (θseq_pos P p) hno' hle le_rfl h0.2

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.ValidSeq.param_u := @BCFGJPSSV26.Greedy.ValidSeq.param_u
