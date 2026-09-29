-- Prove2me | solution 1 for Freiman.late_route_from_checks
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T19:32:58.483825+00:00
-- url     : https://prove2.me/submissions/6cc49f84-da8c-4bed-b446-5baac85c8b0f

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Basic
import Mathlib.Order.SetNotation

set_option maxHeartbeats 1000000
set_option maxRecDepth 40000

open Freiman

namespace M7Last

lemma inter_icc_nonempty {a1 b1 a2 b2 : ℝ} (h1 : a1 ≤ b1) (h2 : a2 ≤ b2)
    (h3 : a2 ≤ b1) (h4 : a1 ≤ b2) : (Set.Icc a1 b1 ∩ Set.Icc a2 b2).Nonempty :=
  ⟨max a1 a2, ⟨le_max_left _ _, max_le h1 h3⟩, ⟨le_max_right _ _, max_le h4 h2⟩⟩

lemma chain_of_zip {α : Type*} (R : α → α → Prop) : ∀ (l : List α),
    (∀ x ∈ l.zip l.tail, R x.1 x.2) → List.IsChain R l
  | [] => fun _ => by simp
  | [_] => fun _ => by simp
  | a :: b :: t => fun h => by
      refine List.isChain_cons_cons.mpr ⟨h (a, b) (by simp), chain_of_zip R (b :: t) ?_⟩
      intro x hx
      refine h x ?_
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons]
      exact Or.inr (by simpa using hx)

end M7Last

theorem solution (ho : ∀ p : LowerPair, lowerEndpoint p false ≤ lowerEndpoint p true) (p : LowerPair) (path : LatePath) (hm : ¬ lowerMixed p)
    (hv : latePathValid lateCatalog path)
    (ha : lowerGood (lowerChild p ([2],[2])) ∧ lowerGood (lowerChild p ([2],[1])))
    (hn : ∀ n ∈ path.normalizations, lateNormalizationHolds p n)
    (hf : lateForkAlignment p path)
    (hc : ∀ c ∈ path.checks, lateSpecHolds p (lateCheckSpec lateCatalog c)) :
    lowerLateRouteValid p path.route := by
  classical
  obtain ⟨hlen2, _hlenC, _hnodup, hhead, hlast, hmemc, _hreq, _hinc, hnormlab, _hnb,
    hchecks, _hcv, _himp⟩ := hv
  -- every expected spec is realised by one of the stored checks
  have hspec : ∀ S ∈ lateExpectedSpecs path, lateSpecHolds p S := by
    intro S hS
    rw [← hchecks] at hS
    obtain ⟨c, hcmem, hEq⟩ := List.mem_map.mp hS
    exact hEq ▸ hc c hcmem
  -- the non-strict content of a spec with first-upper / second-lower shape
  have K : ∀ (a b : LowerPair) (s : Bool),
      ((a, true, b, false, s) : LateSpec) ∈ lateExpectedSpecs path →
      lateActualEndpoint p b false ≤ lateActualEndpoint p a true := by
    intro a b s hmem
    have H := hspec _ hmem
    cases s with
    | false => first | exact H | simpa using H
    | true => first | exact le_of_lt H | exact le_of_lt (by simpa using H)
  -- two opposite specs give a nonempty intersection of the two covers
  have both : ∀ (a b : LowerPair) (s1 s2 : Bool),
      ((a, true, b, false, s1) : LateSpec) ∈ lateExpectedSpecs path →
      ((b, true, a, false, s2) : LateSpec) ∈ lateExpectedSpecs path →
      (lowerCover (lowerHistoryAppend (lowerNormalize p) a) ∩
        lowerCover (lowerHistoryAppend (lowerNormalize p) b)).Nonempty := by
    intro a b s1 s2 h1 h2
    have K1 := K a b s1 h1
    have K2 := K b a s2 h2
    have P : lowerEndpoint (lowerHistoryAppend (lowerNormalize p) b) false ≤
          lowerEndpoint (lowerHistoryAppend (lowerNormalize p) a) true ∧
        lowerEndpoint (lowerHistoryAppend (lowerNormalize p) a) false ≤
          lowerEndpoint (lowerHistoryAppend (lowerNormalize p) b) true := by
      by_cases hpar : (lowerNormalize p).1.length % 2 = 1
      · have hAE : ∀ (w : LowerPair) (u : Bool), lateActualEndpoint p w u
            = -lowerEndpoint (lowerHistoryAppend (lowerNormalize p) w) (!u) := by
          intro w u
          simp [lateActualEndpoint, lowerHistoryEndpointReal, lowerHistoryCommonOdd,
            lateContext, hpar]
        rw [hAE, hAE] at K1
        rw [hAE, hAE] at K2
        simp only [Bool.not_false, Bool.not_true, neg_le_neg_iff] at K1 K2
        exact ⟨K2, K1⟩
      · have hAE : ∀ (w : LowerPair) (u : Bool), lateActualEndpoint p w u
            = lowerEndpoint (lowerHistoryAppend (lowerNormalize p) w) u := by
          intro w u
          simp [lateActualEndpoint, lowerHistoryEndpointReal, lowerHistoryCommonOdd,
            lateContext, hpar]
        rw [hAE, hAE] at K1
        rw [hAE, hAE] at K2
        exact ⟨K1, K2⟩
    exact M7Last.inter_icc_nonempty (ho _) (ho _) P.1 P.2
  -- structure of the route: head, middle (the normalised labels), last
  obtain ⟨a0, rest, hr⟩ : ∃ a0 rest, path.route = a0 :: rest := by
    cases hcase : path.route with
    | nil => rw [hcase] at hlen2; simp at hlen2
    | cons a0 rest => exact ⟨a0, rest, rfl⟩
  have ha0 : a0 = (([2], [2]) : LowerLabel) := by
    rw [hr] at hhead; simpa using hhead
  obtain ⟨b0, tl, hrest⟩ : ∃ b0 tl, rest = b0 :: tl := by
    cases hcase : rest with
    | nil => rw [hr, hcase] at hlen2; simp at hlen2
    | cons b0 tl => exact ⟨b0, tl, rfl⟩
  have hdl : path.route.dropLast ++ [(([2], [1]) : LowerLabel)] = path.route :=
    List.dropLast_append_getLast? _ hlast
  have hdl2 : path.route.dropLast = a0 :: path.route.tail.dropLast := by
    rw [hr, hrest]; simp
  have hdecomp : path.route = a0 :: (path.route.tail.dropLast ++ [(([2], [1]) : LowerLabel)]) := by
    conv_lhs => rw [← hdl, hdl2]
    simp
  -- goodness of each child along the route
  have hgood : ∀ l ∈ path.route, lowerGood (lowerChild p l) := by
    intro l hl
    rw [hdecomp] at hl
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | hl | rfl
    · rw [ha0]; exact ha.1
    · -- l is a normalised interior label: use the fork specs
      rw [← hnormlab] at hl
      obtain ⟨n, hnmem, hnl⟩ := List.mem_map.mp hl
      have hcov : ∀ d : ℕ+, d ∈ ([1, 2] : List ℕ+) →
          lowerCover (lowerChild (lowerChild p n.label) ([d], [])) =
            lowerCover (lowerHistoryAppend (lowerNormalize p) (lateForkWords n d)) := by
        intro d hd
        show Set.Icc _ _ = Set.Icc _ _
        rw [hf n hnmem d hd false, hf n hnmem d hd true]
      have h1mem : ((lateForkWords n 1, true, lateForkWords n 2, false, true) : LateSpec)
          ∈ lateExpectedSpecs path := by
        refine List.mem_append_left _ (List.mem_append_right _ ?_)
        exact List.mem_flatMap.mpr ⟨n, hnmem, by simp⟩
      have h2mem : ((lateForkWords n 2, true, lateForkWords n 1, false, true) : LateSpec)
          ∈ lateExpectedSpecs path := by
        refine List.mem_append_left _ (List.mem_append_right _ ?_)
        exact List.mem_flatMap.mpr ⟨n, hnmem, by simp⟩
      have := both _ _ true true h1mem h2mem
      rw [← hcov 1 (by simp), ← hcov 2 (by simp)] at this
      rw [← hnl]
      exact this
    · exact ha.2
  refine ⟨fun l hl => ⟨hmemc l hl, hgood l hl⟩, hhead, hlast, ?_⟩
  -- the contact chain
  refine M7Last.chain_of_zip _ path.route ?_
  rintro ⟨l, m⟩ hx
  have h1mem : ((lateWords l, true, lateWords m, false, false) : LateSpec)
      ∈ lateExpectedSpecs path := by
    refine List.mem_append_right _ ?_
    exact List.mem_flatMap.mpr ⟨(l, m), hx, by simp⟩
  have h2mem : ((lateWords m, true, lateWords l, false, false) : LateSpec)
      ∈ lateExpectedSpecs path := by
    refine List.mem_append_right _ ?_
    exact List.mem_flatMap.mpr ⟨(l, m), hx, by simp⟩
  have := both _ _ false false h1mem h2mem
  exact this
