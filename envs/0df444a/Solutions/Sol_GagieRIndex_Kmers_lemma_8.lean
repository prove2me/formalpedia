-- Prove2me | solution 1 for GagieRIndex.Kmers.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-13T13:35:15.834067+00:00
-- url     : https://prove2.me/submissions/1c459f60-214d-43e3-b92f-0d9c56e4511c

import Mathlib
import Definitions.Def_GagieRIndex_Kmers_Smers

set_option autoImplicit false

namespace Lemma8Aux

/-- BWT at `p` when `SA p ≠ 1`. -/
theorem bwt_eq_of_ne (n : ℕ) (T SA : ℕ → ℕ) {p : ℕ} (hp : SA p ≠ 1) :
    GagieRIndex.Locate.bwt n T SA p = T (SA p - 1) := by
  unfold GagieRIndex.Locate.bwt
  rw [if_neg hp]

/-- `textPos` at `p` when `SA p ≠ 1`. -/
theorem textPos_eq_of_ne (n : ℕ) (SA : ℕ → ℕ) {p : ℕ} (hp : SA p ≠ 1) :
    GagieRIndex.Locate.textPos n SA p = SA p - 1 := by
  unfold GagieRIndex.Locate.textPos
  rw [if_neg hp]

/-- `SA` is surjective on `[1,n]` (finite injectivity + range). -/
theorem sa_surj (n : ℕ) (T SA : ℕ → ℕ)
    (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    {i : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) :
    ∃ p, 1 ≤ p ∧ p ≤ n ∧ SA p = i := by
  obtain ⟨hSA1, hSAinj, -⟩ := hSA
  have hsub : (Finset.Icc 1 n).image SA ⊆ Finset.Icc 1 n := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h1p, hpn⟩ := Finset.mem_Icc.mp hp
    exact Finset.mem_Icc.mpr (hSA1 p h1p hpn)
  have hcard : ((Finset.Icc 1 n).image SA).card = (Finset.Icc 1 n).card :=
    Finset.card_image_of_injOn (by
      intro x hx y hy hxy
      rw [Finset.mem_coe] at hx hy
      exact hSAinj (Set.mem_Icc.mpr (Finset.mem_Icc.mp hx))
        (Set.mem_Icc.mpr (Finset.mem_Icc.mp hy)) hxy)
  have himg : (Finset.Icc 1 n).image SA = Finset.Icc 1 n :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have hiimg : i ∈ (Finset.Icc 1 n).image SA := by
    rw [himg]; exact Finset.mem_Icc.mpr ⟨hi1, hin⟩
  obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp hiimg
  exact ⟨p, (Finset.mem_Icc.mp hp).1, (Finset.mem_Icc.mp hp).2, hpi⟩

/-- Length of a suffix list. -/
theorem suffix_length (n : ℕ) (T : ℕ → ℕ) (a : ℕ) :
    (GagieRIndex.Locate.suffix n T a).length = n + 1 - a := by
  simp [GagieRIndex.Locate.suffix]

/-- The `k`-th entry of a suffix list (when in range). -/
theorem suffix_get (n : ℕ) (T : ℕ → ℕ) (a k : ℕ) (hk : a + k ≤ n) :
    (GagieRIndex.Locate.suffix n T a)[k]'(by
      rw [suffix_length]; omega) = T (a + k) := by
  unfold GagieRIndex.Locate.suffix
  rw [List.getElem_map]
  simp

/-- A pattern starting at `a` prefixes the suffix at `a`. -/
theorem self_prefix (n : ℕ) (T : ℕ → ℕ) (a d : ℕ) (hd : a + d ≤ n + 1) :
    (List.range d).map (fun k => T (a + k)) <+:
      GagieRIndex.Locate.suffix n T a := by
  refine ⟨(GagieRIndex.Locate.suffix n T a).drop d, ?_⟩
  have htake : (List.range d).map (fun k => T (a + k)) =
      (GagieRIndex.Locate.suffix n T a).take d := by
    unfold GagieRIndex.Locate.suffix
    rw [← List.map_take, List.take_range, min_eq_left (by omega : d ≤ n + 1 - a)]
  rw [htake, List.take_append_drop]

/-- Pointwise equality of length-`d` windows gives a prefix. -/
theorem pointwise_to_prefix (n : ℕ) (T : ℕ → ℕ) (a b d : ℕ)
    (hd : a + d ≤ n + 1)
    (h : ∀ t, t < d → T (a + t) = T (b + t)) :
    (List.range d).map (fun k => T (b + k)) <+:
      GagieRIndex.Locate.suffix n T a := by
  have hEq : (List.range d).map (fun k => T (b + k)) =
      (List.range d).map (fun k => T (a + k)) := by
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    exact (h k hk).symm
  rw [hEq]
  exact self_prefix n T a d hd

/-- Read off one entry from a prefix of a suffix. -/
theorem prefix_get (n : ℕ) (T : ℕ → ℕ) (a b d k : ℕ)
    (hpre : (List.range d).map (fun k => T (b + k)) <+:
      GagieRIndex.Locate.suffix n T a)
    (hk : k < d) (hka : a + k ≤ n) :
    T (a + k) = T (b + k) := by
  obtain ⟨rest, hr⟩ := hpre
  have hlenP : k < ((List.range d).map (fun k => T (b + k))).length := by
    simp; omega
  have e : ((List.range d).map (fun k => T (b + k)) ++ rest)[k]? =
      (GagieRIndex.Locate.suffix n T a)[k]? := by rw [← hr]
  rw [List.getElem?_append_left hlenP, List.getElem?_map, List.getElem?_range hk] at e
  simp at e
  have hk2 : k < n + 1 - a := by omega
  have e2 : (GagieRIndex.Locate.suffix n T a)[k]? = some (T (a + k)) := by
    unfold GagieRIndex.Locate.suffix
    rw [List.getElem?_map, List.getElem?_range hk2]
    simp
  rw [e2] at e
  exact (Option.some_inj.mp e).symm

end Lemma8Aux


namespace Lemma8Aux

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

/-- Core convexity fact, by induction on the pattern. -/
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

/-- Convexity of the `P`-prefix set along the suffix array. -/
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
`sp = n+1 > n = ep` when the set is empty. Strengthened with `1 ≤ sp ∧ ep ≤ n`. -/
theorem solution_main (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T)
    (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (P : List ℕ) :
    ∃ sp ep, 1 ≤ sp ∧ ep ≤ n ∧ ∀ p, 1 ≤ p → p ≤ n →
      (P <+: GagieRIndex.Locate.suffix n T (SA p) ↔ sp ≤ p ∧ p ≤ ep) := by
  classical
  obtain ⟨h1n, -, -, -⟩ := hT
  by_cases hP : P = []
  · refine ⟨1, n, le_rfl, le_rfl, fun p h1p hpn => ?_⟩
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
      refine ⟨S.min' hne, S.max' hne, hsp1, hepn, fun p h1p hpn => ?_⟩
      constructor
      · intro hAp
        have hpS : p ∈ S :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1p, hpn⟩, hAp⟩
        exact ⟨S.min'_le p hpS, S.le_max' p hpS⟩
      · rintro ⟨hle, hle'⟩
        exact prefix_convex n T SA P hSA hP hsp1 hspn hep1 hepn hle hle' hspA hepA
    · refine ⟨n + 1, n, by omega, le_rfl, fun p h1p hpn => ?_⟩
      constructor
      · intro hAp
        have hpS : p ∈ S :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1p, hpn⟩, hAp⟩
        exact (hne ⟨p, hpS⟩).elim
      · rintro ⟨hle, hle'⟩
        omega

end SuffixRangeAux

namespace SampledCharAux

variable (n : ℕ) (T SA : ℕ → ℕ)

/-- `textPos` maps `[1,n]` back into `[1,n]`. -/
theorem textPos_mem_Icc (h1n : 1 ≤ n)
    (hSA1 : ∀ p, 1 ≤ p → p ≤ n → 1 ≤ SA p ∧ SA p ≤ n)
    {p : ℕ} (hp : p ∈ Finset.Icc 1 n) :
    GagieRIndex.Locate.textPos n SA p ∈ Finset.Icc 1 n := by
  obtain ⟨h1p, hpn⟩ := Finset.mem_Icc.mp hp
  obtain ⟨hSAp1, hSApn⟩ := hSA1 p h1p hpn
  unfold GagieRIndex.Locate.textPos
  split
  · rw [Finset.mem_Icc]; exact ⟨h1n, le_rfl⟩
  · rw [Finset.mem_Icc]; constructor <;> omega

/-- `textPos` is injective on `[1,n]` (uses `SA` injectivity and range). -/
theorem textPos_injOn (h1n : 1 ≤ n)
    (hSA1 : ∀ p, 1 ≤ p → p ≤ n → 1 ≤ SA p ∧ SA p ≤ n)
    (hSAinj : Set.InjOn SA (Set.Icc 1 n)) :
    Set.InjOn (GagieRIndex.Locate.textPos n SA) ↑(Finset.Icc 1 n) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe] at hx hy
  obtain ⟨h1x, hxn⟩ := Finset.mem_Icc.mp hx
  obtain ⟨h1y, hyn⟩ := Finset.mem_Icc.mp hy
  obtain ⟨hSAx1, hSAxn⟩ := hSA1 x h1x hxn
  obtain ⟨hSAy1, hSAyn⟩ := hSA1 y h1y hyn
  have hmemx : x ∈ Set.Icc 1 n := Set.mem_Icc.mpr ⟨h1x, hxn⟩
  have hmemy : y ∈ Set.Icc 1 n := Set.mem_Icc.mpr ⟨h1y, hyn⟩
  unfold GagieRIndex.Locate.textPos at hxy
  by_cases hxx : SA x = 1 <;> by_cases hyy : SA y = 1
  · rw [if_pos hxx, if_pos hyy] at hxy
    have hSx : SA x = SA y := by rw [hxx, hyy]
    exact hSAinj hmemx hmemy hSx
  · rw [if_pos hxx, if_neg hyy] at hxy
    omega
  · rw [if_neg hxx, if_pos hyy] at hxy
    omega
  · rw [if_neg hxx, if_neg hyy] at hxy
    have hSxy : SA x = SA y := by omega
    exact hSAinj hmemx hmemy hSxy

/-- `BWT[p]` is the character at text position `textPos p`. -/
theorem bwt_eq (p : ℕ) :
    GagieRIndex.Locate.bwt n T SA p = T (GagieRIndex.Locate.textPos n SA p) := by
  unfold GagieRIndex.Locate.bwt GagieRIndex.Locate.textPos
  by_cases h : SA p = 1 <;> simp [h]

/-- The image of `[1,n]` under `textPos` is all of `[1,n]` (finite injectivity). -/
theorem textPos_image (h1n : 1 ≤ n)
    (hSA1 : ∀ p, 1 ≤ p → p ≤ n → 1 ≤ SA p ∧ SA p ≤ n)
    (hSAinj : Set.InjOn SA (Set.Icc 1 n)) :
    (Finset.Icc 1 n).image (GagieRIndex.Locate.textPos n SA) = Finset.Icc 1 n := by
  have hsub : (Finset.Icc 1 n).image (GagieRIndex.Locate.textPos n SA) ⊆ Finset.Icc 1 n := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact textPos_mem_Icc n SA h1n hSA1 hp
  have hcard : ((Finset.Icc 1 n).image (GagieRIndex.Locate.textPos n SA)).card =
      (Finset.Icc 1 n).card :=
    Finset.card_image_of_injOn (textPos_injOn n SA h1n hSA1 hSAinj)
  apply Finset.eq_of_subset_of_card_le hsub
  exact le_of_eq hcard.symm

/-- Main proof: the last BWT occurrence of `T i` sits at a run end, whose
`textPos` is a sampled position carrying `T i`. -/
theorem sampled_character_main (σ : ℕ) (hT : GagieRIndex.Locate.IsText n σ T)
    (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    ∃ i' ∈ GagieRIndex.Locate.sampled n T SA, T i' = T i := by
  obtain ⟨h1n, -, -, -⟩ := hT
  obtain ⟨hSA1, hSAinj, -⟩ := hSA
  have himg := textPos_image n SA h1n hSA1 hSAinj
  have hiimg : i ∈ (Finset.Icc 1 n).image (GagieRIndex.Locate.textPos n SA) := by
    rw [himg]; exact Finset.mem_Icc.mpr ⟨hi, hin⟩
  obtain ⟨p₀, hp₀, hp₀i⟩ := Finset.mem_image.mp hiimg
  set S := (Finset.Icc 1 n).filter
    (fun p => GagieRIndex.Locate.bwt n T SA p = T i) with hSdef
  have hne : S.Nonempty := by
    refine ⟨p₀, ?_⟩
    rw [hSdef]
    refine Finset.mem_filter.mpr ⟨hp₀, ?_⟩
    rw [bwt_eq n T SA p₀, hp₀i]
  set q := S.max' hne with hqdef
  have hqS : q ∈ S := S.max'_mem hne
  have hqmem : q ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hqS).1
  have hqbwt : GagieRIndex.Locate.bwt n T SA q = T i := (Finset.mem_filter.mp hqS).2
  obtain ⟨h1q, hqn⟩ := Finset.mem_Icc.mp hqmem
  have hrunend : GagieRIndex.Locate.IsRunEnd n T SA q := by
    refine ⟨h1q, hqn, ?_⟩
    by_cases hqn' : q = n
    · exact Or.inl hqn'
    · refine Or.inr ?_
      intro hcon
      have hq1mem : q + 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hq1S : q + 1 ∈ S := by
        rw [hSdef]
        refine Finset.mem_filter.mpr ⟨hq1mem, ?_⟩
        rw [hcon, hqbwt]
      have hle : q + 1 ≤ q := Finset.le_max' S (q + 1) hq1S
      omega
  have hqfilter : q ∈ (Finset.Icc 1 n).filter
      (fun p => GagieRIndex.Locate.IsRunStart n T SA p ∨
        GagieRIndex.Locate.IsRunEnd n T SA p) :=
    Finset.mem_filter.mpr ⟨hqmem, Or.inr hrunend⟩
  have hqsampled : GagieRIndex.Locate.textPos n SA q ∈
      GagieRIndex.Locate.sampled n T SA := by
    unfold GagieRIndex.Locate.sampled
    exact Finset.mem_image.mpr ⟨q, hqfilter, rfl⟩
  exact ⟨GagieRIndex.Locate.textPos n SA q, hqsampled,
    by rw [← bwt_eq n T SA q]; exact hqbwt⟩

end SampledCharAux

/-- Sampled positions lie in `[1,n]`. -/
theorem sampled_mem_Icc (n : ℕ) (T SA : ℕ → ℕ) (h1n : 1 ≤ n)
    (hSA1 : ∀ p, 1 ≤ p → p ≤ n → 1 ≤ SA p ∧ SA p ≤ n)
    {x : ℕ} (hx : x ∈ GagieRIndex.Locate.sampled n T SA) : 1 ≤ x ∧ x ≤ n := by
  unfold GagieRIndex.Locate.sampled at hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_Icc.mp
    (SampledCharAux.textPos_mem_Icc n SA h1n hSA1 (Finset.mem_filter.mp hp).1)

/-- Shared finish: an SA-position `q` whose BWT symbol is `T i` and which is a
run boundary yields the primary occurrence `SA q - 1` (its own `textPos`). -/
theorem finish_of_run (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T)
    (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (i j q : ℕ) (hi : 1 ≤ i) (hin : i < n) (hij : i ≤ j) (hj : j ≤ n)
    (hTne : T i ≠ 1)
    (hq1 : 1 ≤ q) (hqn : q ≤ n)
    (hpre : (List.range (j - (i + 1) + 1)).map (fun k => T (i + 1 + k)) <+:
      GagieRIndex.Locate.suffix n T (SA q))
    (hqBWT : GagieRIndex.Locate.bwt n T SA q = T i)
    (hqRun : GagieRIndex.Locate.IsRunStart n T SA q ∨
      GagieRIndex.Locate.IsRunEnd n T SA q) :
    ∃ i', GagieRIndex.Kmers.IsPrimary n T SA i' (i' + (j - i)) ∧
      ∀ t ≤ j - i, T (i' + t) = T (i + t) := by
  obtain ⟨h1n, -, hTn, -⟩ := hT
  obtain ⟨hSA1, -, -⟩ := hSA
  obtain ⟨hSAq1, hSAqn⟩ := hSA1 q hq1 hqn
  have hSAqne : SA q ≠ 1 := by
    intro hcon
    unfold GagieRIndex.Locate.bwt at hqBWT
    rw [if_pos hcon, hTn] at hqBWT
    exact hTne hqBWT.symm
  have hprelen := List.IsPrefix.length_le hpre
  rw [List.length_map, List.length_range, suffix_length] at hprelen
  have hSAqd : SA q + (j - i) ≤ n + 1 := by omega
  have hTi' : T (SA q - 1) = T i := by
    rw [← hqBWT, bwt_eq_of_ne n T SA hSAqne]
  have hi'samp : SA q - 1 ∈ GagieRIndex.Locate.sampled n T SA := by
    have htp : GagieRIndex.Locate.textPos n SA q = SA q - 1 :=
      textPos_eq_of_ne n SA hSAqne
    rw [← htp]
    unfold GagieRIndex.Locate.sampled
    exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hq1, hqn⟩, hqRun⟩, rfl⟩
  refine ⟨SA q - 1, ⟨by omega, by omega, by omega,
    ⟨SA q - 1, hi'samp, le_rfl, by omega⟩⟩, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · subst ht0
    simpa using hTi'
  · have ht1 : t - 1 < j - (i + 1) + 1 := by omega
    have hget := prefix_get n T (SA q) (i + 1) (j - (i + 1) + 1) (t - 1)
      hpre ht1 (by omega)
    have e1 : SA q - 1 + t = SA q + (t - 1) := by omega
    have e2 : i + 1 + (t - 1) = i + t := by omega
    rw [e1, ← e2]
    exact hget

end Lemma8Aux

namespace Lemma8Aux

/-- Strong induction on `d = j - i`: base case is `sampled_character`;
the step splits on whether the BWT is constant `T i` on the SA-range of
`T[i+1..j]` (then shift the IH primary occurrence left by one) or not
(then a run boundary in the range yields a primary occurrence directly). -/
theorem main (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T)
    (hSA : GagieRIndex.Locate.IsSuffixArray n T SA) :
    ∀ d, ∀ i j, j - i = d → 1 ≤ i → i ≤ j → j ≤ n →
      ∃ i', GagieRIndex.Kmers.IsPrimary n T SA i' (i' + (j - i)) ∧
        ∀ t ≤ j - i, T (i' + t) = T (i + t) := by
  intro d
  refine Nat.strong_induction_on d ?_
  intro d ih
  intro i j hd hi hij hj
  -- `obtain` clears the originals; copy first, destructure the copies.
  have hTcopy := hT
  have hSAcopy := hSA
  obtain ⟨h1n, hTrange, hTn, hTne⟩ := hTcopy
  obtain ⟨hSA1, hSAinj, -⟩ := hSAcopy
  by_cases hd0 : d = 0
  · have hji : j = i := by omega
    obtain ⟨i', hi'samp, hi'T⟩ :=
      SampledCharAux.sampled_character_main n T SA σ hT hSA i hi (by omega)
    have hi'bnd := sampled_mem_Icc n T SA h1n hSA1 hi'samp
    refine ⟨i', ⟨hi'bnd.1, by omega, by omega,
      ⟨i', hi'samp, by omega, by omega⟩⟩, ?_⟩
    intro t ht
    have ht0 : t = 0 := by omega
    subst ht0
    simpa using hi'T
  · have hdpos : 0 < d := by omega
    have hij' : i < j := by omega
    have hin : i < n := by omega
    have hTi_ne : T i ≠ 1 := hTne i hi hin
    have hIH := ih (d - 1) (by omega) (i + 1) j (by omega) (by omega) (by omega) hj
    obtain ⟨i1', hPrim1, hpt1⟩ := hIH
    have hPrim1' : 1 ≤ i1' ∧ i1' ≤ i1' + (j - (i + 1)) ∧
        i1' + (j - (i + 1)) ≤ n ∧
        ∃ x ∈ GagieRIndex.Locate.sampled n T SA,
          i1' ≤ x ∧ x ≤ i1' + (j - (i + 1)) := hPrim1
    obtain ⟨hi1'1, -, hi1'n, ⟨x, hxsamp, hi1'x, hxi1'⟩⟩ := hPrim1'
    obtain ⟨sp, ep, hsp1, hepn, hrange⟩ :=
      SuffixRangeAux.solution_main n σ T SA hT hSA
        ((List.range (j - (i + 1) + 1)).map (fun k => T (i + 1 + k)))
    obtain ⟨p0, hp01, hp0n, hp0SA⟩ :=
      sa_surj n T SA hSA (by omega : 1 ≤ i + 1) (by omega : i + 1 ≤ n)
    have hpre0 : (List.range (j - (i + 1) + 1)).map (fun k => T (i + 1 + k)) <+:
        GagieRIndex.Locate.suffix n T (i + 1) :=
      self_prefix n T (i + 1) (j - (i + 1) + 1) (by omega)
    have hp0range : sp ≤ p0 ∧ p0 ≤ ep := by
      apply (hrange p0 hp01 hp0n).mp
      rw [hp0SA]
      exact hpre0
    have hBWT0 : GagieRIndex.Locate.bwt n T SA p0 = T i := by
      have hne : SA p0 ≠ 1 := by rw [hp0SA]; omega
      rw [bwt_eq_of_ne n T SA hne, hp0SA, Nat.add_sub_cancel]
    by_cases hall : ∀ p, sp ≤ p → p ≤ ep →
        GagieRIndex.Locate.bwt n T SA p = T i
    · -- Case A: BWT constant `T i` on the range; shift the IH occurrence left.
      have hpre1 : (List.range (j - (i + 1) + 1)).map (fun k => T (i + 1 + k)) <+:
          GagieRIndex.Locate.suffix n T i1' :=
        pointwise_to_prefix n T i1' (i + 1) (j - (i + 1) + 1) (by omega)
          (fun t ht => hpt1 t (by omega))
      obtain ⟨p1, hp11, hp1n, hp1SA⟩ :=
        sa_surj n T SA hSA hi1'1 (by omega : i1' ≤ n)
      have hp1range : sp ≤ p1 ∧ p1 ≤ ep := by
        apply (hrange p1 hp11 hp1n).mp
        rw [hp1SA]
        exact hpre1
      have hBWT1 : GagieRIndex.Locate.bwt n T SA p1 = T i :=
        hall p1 hp1range.1 hp1range.2
      have hi1'ne : i1' ≠ 1 := by
        intro hcon
        have hSA1' : SA p1 = 1 := by rw [hp1SA]; exact hcon
        unfold GagieRIndex.Locate.bwt at hBWT1
        rw [if_pos hSA1'] at hBWT1
        rw [hTn] at hBWT1
        exact hTi_ne hBWT1.symm
      have hTi1 : T (i1' - 1) = T i := by
        have hne : SA p1 ≠ 1 := by rw [hp1SA]; exact hi1'ne
        rw [← hBWT1, bwt_eq_of_ne n T SA hne, hp1SA]
      refine ⟨i1' - 1, ⟨by omega, by omega, by omega,
        ⟨x, hxsamp, by omega, by omega⟩⟩, ?_⟩
      intro t ht
      by_cases ht0 : t = 0
      · subst ht0
        simpa using hTi1
      · have ht1 : t - 1 ≤ j - (i + 1) := by omega
        have e1 := hpt1 (t - 1) ht1
        have e2 : i1' - 1 + t = i1' + (t - 1) := by omega
        have e3 : i + 1 + (t - 1) = i + t := by omega
        rw [e2, ← e3]
        exact e1
    · -- Case B: some BWT symbol in the range differs from `T i`.
      push_neg at hall
      by_cases hsp : GagieRIndex.Locate.bwt n T SA sp = T i
      · -- Least non-`T i` position `m` in the range; `m - 1` is a run end in the range.
        obtain ⟨pstar, hpstar1, hpstar2, hBWTstar⟩ := hall
        set S2 := (Finset.Icc sp ep).filter
          (fun p => GagieRIndex.Locate.bwt n T SA p ≠ T i) with hS2def
        have hS2ne : S2.Nonempty := ⟨pstar, by
          rw [hS2def]
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hpstar1, hpstar2⟩, hBWTstar⟩⟩
        set m := S2.min' hS2ne with hmdef
        have hminmem : m ∈ S2 := S2.min'_mem hS2ne
        have hminIcc : m ∈ Finset.Icc sp ep := (Finset.mem_filter.mp hminmem).1
        have hminBWT : GagieRIndex.Locate.bwt n T SA m ≠ T i :=
          (Finset.mem_filter.mp hminmem).2
        have hminrange := Finset.mem_Icc.mp hminIcc
        have hmin_gt : sp < m := by
          by_contra hcon
          have hEq : m = sp := by omega
          rw [hEq] at hminBWT
          exact hminBWT hsp
        have hqBWT : GagieRIndex.Locate.bwt n T SA (m - 1) = T i := by
          by_contra hcon
          have hmem : m - 1 ∈ S2 := by
            rw [hS2def]
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hcon⟩
          have hle := S2.min'_le (m - 1) hmem
          omega
        have hqRun : GagieRIndex.Locate.IsRunEnd n T SA (m - 1) := by
          refine ⟨by omega, by omega, Or.inr ?_⟩
          have e : m - 1 + 1 = m := by omega
          rw [e, hqBWT]
          exact hminBWT
        have hpreq : (List.range (j - (i + 1) + 1)).map (fun k => T (i + 1 + k)) <+:
            GagieRIndex.Locate.suffix n T (SA (m - 1)) :=
          (hrange (m - 1) (by omega) (by omega)).mpr ⟨by omega, by omega⟩
        exact finish_of_run n σ T SA hT hSA i j (m - 1) hi hin hij hj hTi_ne
          (by omega) (by omega) hpreq hqBWT (Or.inr hqRun)
      · -- `sp` itself is non-`T i`; the least `T i` position `q` is a run start.
        set Q := (Finset.Icc sp ep).filter
          (fun p => GagieRIndex.Locate.bwt n T SA p = T i) with hQdef
        have hQne : Q.Nonempty := ⟨p0, by
          rw [hQdef]
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hp0range, hBWT0⟩⟩
        set q := Q.min' hQne with hqdef
        have hqmem : q ∈ Q := Q.min'_mem hQne
        have hqIcc : q ∈ Finset.Icc sp ep := (Finset.mem_filter.mp hqmem).1
        have hqBWT : GagieRIndex.Locate.bwt n T SA q = T i :=
          (Finset.mem_filter.mp hqmem).2
        have hqrange := Finset.mem_Icc.mp hqIcc
        have hq_gt : sp < q := by
          by_contra hcon
          have hEq : q = sp := by omega
          rw [hEq] at hqBWT
          exact hsp hqBWT
        have hqRun : GagieRIndex.Locate.IsRunStart n T SA q := by
          refine ⟨by omega, by omega, Or.inr ?_⟩
          have hnot : q - 1 ∉ Q := by
            intro hmem
            have hle := Q.min'_le (q - 1) hmem
            omega
          have hmemIcc : q - 1 ∈ Finset.Icc sp ep :=
            Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          have hne : GagieRIndex.Locate.bwt n T SA (q - 1) ≠ T i := by
            intro hcon
            exact hnot (by
              rw [hQdef]
              exact Finset.mem_filter.mpr ⟨hmemIcc, hcon⟩)
          rw [hqBWT]
          exact hne
        have hpreq : (List.range (j - (i + 1) + 1)).map (fun k => T (i + 1 + k)) <+:
            GagieRIndex.Locate.suffix n T (SA q) :=
          (hrange q (by omega) (by omega)).mpr ⟨hqrange.1, hqrange.2⟩
        exact finish_of_run n σ T SA hT hSA i j q hi hin hij hj hTi_ne
          (by omega) (by omega) hpreq hqBWT (Or.inl hqRun)

end Lemma8Aux

open GagieRIndex.Kmers in
theorem solution (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n) :
    ∃ i', IsPrimary n T SA i' (i' + (j - i)) ∧
      ∀ t ≤ j - i, T (i' + t) = T (i + t) :=
  Lemma8Aux.main n σ T SA hT hSA (j - i) i j rfl hi hij hj

theorem GagieRIndex.Kmers.lemma_8 (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ n) :
    ∃ i', GagieRIndex.Kmers.IsPrimary n T SA i' (i' + (j - i)) ∧
      ∀ t ≤ j - i, T (i' + t) = T (i + t) :=
  solution n σ T SA hT hSA i j hi hij hj
