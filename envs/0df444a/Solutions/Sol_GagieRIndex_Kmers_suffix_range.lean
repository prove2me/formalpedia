-- Prove2me | solution 1 for GagieRIndex.Kmers.suffix_range
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-11T17:32:46.233683+00:00
-- url     : https://prove2.me/submissions/87075f1b-4967-4413-993f-36eb8949eb44

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Core

set_option autoImplicit false

namespace SuffixRangeAux

variable (n : ℕ) (T SA : ℕ → ℕ) (P : List ℕ)

/-- The suffix-array order is strictly monotone over `[1,n]` (auxiliary form). -/
theorem suffix_lt_chain_aux (hSA : GagieRIndex.Locate.IsSuffixArray n T SA) :
    ∀ j, j ≤ n → ∀ i, 1 ≤ i → i < j →
      GagieRIndex.Locate.suffix n T (SA i) < GagieRIndex.Locate.suffix n T (SA j) := by
  obtain ⟨-, -, hsort⟩ := hSA
  intro j
  induction j with
  | zero => intro _ i _ hij; omega
  | succ j ih =>
    intro hjn i hi hij
    rcases eq_or_lt_of_le (by omega : i ≤ j) with h | h
    · rw [h]
      exact hsort j (by omega) (by omega)
    · exact (ih (by omega) i hi h).trans_le (le_of_lt (hsort j (by omega) (by omega)))

/-- The suffix-array order is strictly monotone over `[1,n]`. -/
theorem suffix_lt_chain (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjn : j ≤ n) :
    GagieRIndex.Locate.suffix n T (SA i) < GagieRIndex.Locate.suffix n T (SA j) :=
  suffix_lt_chain_aux n T SA hSA j hjn i hi hij

/-- A prefix is `≤` its extension in the lexicographic list order. -/
theorem prefix_le_list {P' s : List ℕ} (h : P' <+: s) : P' ≤ s := by
  obtain ⟨u, rfl⟩ := h
  cases u with
  | nil => simp
  | cons b u =>
    have hlex : List.Lex (· < ·) P' (P' ++ (b :: u)) := by
      induction P' with
      | nil => exact List.Lex.nil
      | cons a P'' ih => exact List.Lex.cons ih
    exact le_of_lt hlex

/-- Core convexity fact, by induction on the pattern: if `Q` prefixes `s_j`,
`Q` is lexicographically smaller than `s_k`, and `s_k` is lexicographically
smaller than `s_j`, then `Q` prefixes `s_k`.
(If the first difference between `Q` and `s_k` favored `s_k`, then `s_j`
— which agrees with `Q` there — would be smaller than `s_k`.) -/
theorem prefix_convex_aux : ∀ (Q : List ℕ) (s_k s_j : List ℕ),
    Q <+: s_j →
    List.Lex (· < ·) Q s_k → List.Lex (· < ·) s_k s_j →
    Q <+: s_k := by
  intro Q
  induction Q with
  | nil =>
    intro s_k s_j _ _ _
    exact List.nil_prefix
  | cons a Q' ih =>
    intro s_k s_j hQj hQk hkj
    obtain ⟨u_j, rfl⟩ := hQj
    rw [List.cons_append] at hkj
    rcases s_k with _ | ⟨b, s_k'⟩
    · cases hQk
    · cases hQk with
      | rel h_rel =>
        cases hkj with
        | rel hkj_rel => exact (lt_asymm h_rel hkj_rel).elim
        | cons hkj_cons => exact (lt_irrefl _ h_rel).elim
      | cons h_cons =>
        cases hkj with
        | rel hkj_rel => exact (lt_irrefl _ hkj_rel).elim
        | cons hkj_cons =>
          have hQ' : Q' <+: s_k' :=
            ih s_k' (Q' ++ u_j) (List.prefix_append Q' u_j) h_cons hkj_cons
          obtain ⟨u, rfl⟩ := hQ'
          exact ⟨u, List.cons_append⟩

/-- Convexity of the `P`-prefix set along the suffix array: if `P` prefixes the
suffixes at `i` and `j`, it prefixes every suffix strictly in between. -/
theorem prefix_convex (hSA : GagieRIndex.Locate.IsSuffixArray n T SA) (hP : P ≠ [])
    {i j k : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) (hj : 1 ≤ j) (hjn : j ≤ n)
    (hik : i ≤ k) (hkj : k ≤ j)
    (hAi : P <+: GagieRIndex.Locate.suffix n T (SA i))
    (hAj : P <+: GagieRIndex.Locate.suffix n T (SA j)) :
    P <+: GagieRIndex.Locate.suffix n T (SA k) := by
  rcases eq_or_lt_of_le hik with rfl | hik'
  · exact hAi
  rcases eq_or_lt_of_le hkj with rfl | hkj'
  · exact hAj
  have hPk : P < GagieRIndex.Locate.suffix n T (SA k) :=
    lt_of_le_of_lt (prefix_le_list hAi)
      (suffix_lt_chain n T SA hSA hi hik' (le_trans hkj hjn))
  have hkj_lt : GagieRIndex.Locate.suffix n T (SA k) <
      GagieRIndex.Locate.suffix n T (SA j) :=
    suffix_lt_chain n T SA hSA (le_trans hi (le_of_lt hik')) hkj' hjn
  exact prefix_convex_aux P _ _ hAj hPk hkj_lt

/-- Main construction: the `P`-prefix positions form `[sp, ep]`, with
`sp = n+1 > n = ep` when the set is empty. -/
theorem solution_main (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T)
    (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (P : List ℕ) :
    ∃ sp ep, ∀ p, 1 ≤ p → p ≤ n →
      (P <+: GagieRIndex.Locate.suffix n T (SA p) ↔ sp ≤ p ∧ p ≤ ep) := by
  classical
  obtain ⟨h1n, -, -, -⟩ := hT
  by_cases hP : P = []
  · refine ⟨1, n, fun p h1p hpn => ?_⟩
    subst hP
    exact ⟨fun _ => ⟨h1p, hpn⟩, fun _ => List.nil_prefix⟩
  · set S : Finset ℕ :=
        (Finset.Icc 1 n).filter
          (fun p => P <+: GagieRIndex.Locate.suffix n T (SA p)) with hSdef
    by_cases hne : S.Nonempty
    · have hspS : S.min' hne ∈ S := S.min'_mem hne
      have hepS : S.max' hne ∈ S := S.max'_mem hne
      have hspA : P <+: GagieRIndex.Locate.suffix n T (SA (S.min' hne)) :=
        (Finset.mem_filter.mp hspS).2
      have hepA : P <+: GagieRIndex.Locate.suffix n T (SA (S.max' hne)) :=
        (Finset.mem_filter.mp hepS).2
      have hsp1 : 1 ≤ S.min' hne :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hspS).1).1
      have hspn : S.min' hne ≤ n :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hspS).1).2
      have hep1 : 1 ≤ S.max' hne :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hepS).1).1
      have hepn : S.max' hne ≤ n :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hepS).1).2
      refine ⟨S.min' hne, S.max' hne, fun p h1p hpn => ?_⟩
      constructor
      · intro hAp
        have hpS : p ∈ S :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1p, hpn⟩, hAp⟩
        exact ⟨S.min'_le p hpS, S.le_max' p hpS⟩
      · rintro ⟨hle, hle'⟩
        exact prefix_convex n T SA P hSA hP hsp1 hspn hep1 hepn hle hle' hspA hepA
    · refine ⟨n + 1, n, fun p h1p hpn => ?_⟩
      constructor
      · intro hAp
        have hpS : p ∈ S :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1p, hpn⟩, hAp⟩
        exact (hne ⟨p, hpS⟩).elim
      · rintro ⟨hle, hle'⟩
        omega

end SuffixRangeAux

/-- The submission entry point (top-level, as the gate requires). -/
theorem solution (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T)
    (hSA : GagieRIndex.Locate.IsSuffixArray n T SA) (P : List ℕ) :
    ∃ sp ep, ∀ p, 1 ≤ p → p ≤ n →
      (P <+: GagieRIndex.Locate.suffix n T (SA p) ↔ sp ≤ p ∧ p ≤ ep) :=
  SuffixRangeAux.solution_main n σ T SA hT hSA P

/-- Ascribed alias matching the published node name. -/
theorem GagieRIndex.Kmers.suffix_range (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T)
    (hSA : GagieRIndex.Locate.IsSuffixArray n T SA) (P : List ℕ) :
    ∃ sp ep, ∀ p, 1 ≤ p → p ≤ n →
      (P <+: GagieRIndex.Locate.suffix n T (SA p) ↔ sp ≤ p ∧ p ≤ ep) :=
  solution n σ T SA hT hSA P
