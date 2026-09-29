-- Prove2me | solution 2 for Freiman.lowerHistory_goodness_from_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T08:15:23.877829+00:00
-- url     : https://prove2.me/submissions/0ba5c63c-97a8-4a45-a543-da821dd6b004

import Definitions.Def_Freiman_lowerHistorySource
import Theorems.Thm_Freiman_lowerHistory_sign_value
import Mathlib.Tactic
import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_cf_value


open Freiman

namespace M7Extreme14

private theorem field_sub (x y : CertField) :
    certFieldVal (certFieldSub x y) = certFieldVal x - certFieldVal y := by
  simp only [certFieldVal, certFieldSub]
  push_cast
  ring

private theorem sign_sub_pos_iff (a b : CertField) :
    0 < lowerHistorySign (certFieldSub b a) ↔ certFieldVal a < certFieldVal b := by
  rw [(lowerHistory_sign_value _).2, field_sub]
  exact sub_pos

private theorem fold_extreme_mem (maximum : Bool) (a : CertField) (zs : List CertField) :
    zs.foldl
        (fun a b =>
          if (decide (0 < lowerHistorySign (certFieldSub b a))) = maximum then b else a)
        a ∈ a :: zs := by
  induction zs generalizing a with
  | nil => simp
  | cons b zs ih =>
      by_cases hc : (decide (0 < lowerHistorySign (certFieldSub b a))) = maximum
      · simp only [List.foldl_cons, if_pos hc, List.mem_cons]
        have h := List.mem_cons.mp (ih b)
        exact Or.elim h (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
      · simp only [List.foldl_cons, if_neg hc, List.mem_cons]
        have h := List.mem_cons.mp (ih a)
        exact Or.elim h Or.inl (fun h => Or.inr (Or.inr h))

private theorem lowerHistoryExtreme_mem (maximum : Bool) (zs : List CertField)
    (hne : zs ≠ []) : lowerHistoryExtreme maximum zs ∈ zs := by
  rcases zs with _ | ⟨a, zs⟩
  · exact (hne rfl).elim
  · simpa [lowerHistoryExtreme] using fold_extreme_mem maximum a zs

private theorem fold_maximum (a : CertField) (zs : List CertField) :
    ∀ z ∈ a :: zs,
      certFieldVal z ≤ certFieldVal
        (zs.foldl
          (fun a b =>
            if (decide (0 < lowerHistorySign (certFieldSub b a))) = true then b else a)
          a) := by
  induction zs generalizing a with
  | nil => simp
  | cons b zs ih =>
      intro z hz
      let next := if (decide (0 < lowerHistorySign (certFieldSub b a))) = true
        then b else a
      have hnext : certFieldVal a ≤ certFieldVal next ∧
          certFieldVal b ≤ certFieldVal next := by
        unfold next
        by_cases h : 0 < lowerHistorySign (certFieldSub b a)
        · have hab : certFieldVal a < certFieldVal b := (sign_sub_pos_iff a b).mp h
          simp [h, le_of_lt hab]
        · have hab : certFieldVal b ≤ certFieldVal a := by
            rw [← not_lt]
            exact fun hlt => h ((sign_sub_pos_iff a b).mpr hlt)
          simp [h, hab]
      have htail := ih next
      have hnle : certFieldVal next ≤ certFieldVal
          (zs.foldl
            (fun a b =>
              if (decide (0 < lowerHistorySign (certFieldSub b a))) = true then b else a)
            next) := htail next (by simp)
      simp only [List.foldl_cons]
      obtain rfl | rfl | hz := by simpa only [List.mem_cons] using hz
      · exact hnext.1.trans hnle
      · exact hnext.2.trans hnle
      · exact htail z (by simp [hz])

private theorem lowerHistoryExtreme_maximum (zs : List CertField) (z : CertField)
    (hz : z ∈ zs) : certFieldVal z ≤ certFieldVal (lowerHistoryExtreme true zs) := by
  rcases zs with _ | ⟨a, zs⟩
  · simp at hz
  · simpa [lowerHistoryExtreme] using fold_maximum a zs z hz

private theorem fold_minimum (a : CertField) (zs : List CertField) :
    ∀ z ∈ a :: zs,
      certFieldVal
        (zs.foldl
          (fun a b =>
            if (decide (0 < lowerHistorySign (certFieldSub b a))) = false then b else a)
          a) ≤ certFieldVal z := by
  induction zs generalizing a with
  | nil => simp
  | cons b zs ih =>
      intro z hz
      let next := if (decide (0 < lowerHistorySign (certFieldSub b a))) = false
        then b else a
      have hnext : certFieldVal next ≤ certFieldVal a ∧
          certFieldVal next ≤ certFieldVal b := by
        unfold next
        by_cases h : 0 < lowerHistorySign (certFieldSub b a)
        · have hab : certFieldVal a ≤ certFieldVal b :=
            le_of_lt ((sign_sub_pos_iff a b).mp h)
          simp [h, hab]
        · have hab : certFieldVal b ≤ certFieldVal a := by
            rw [← not_lt]
            exact fun hlt => h ((sign_sub_pos_iff a b).mpr hlt)
          simp [h, hab]
      have htail := ih next
      have hnle : certFieldVal
          (zs.foldl
            (fun a b =>
              if (decide (0 < lowerHistorySign (certFieldSub b a))) = false then b else a)
            next) ≤ certFieldVal next := htail next (by simp)
      simp only [List.foldl_cons]
      obtain rfl | rfl | hz := by simpa only [List.mem_cons] using hz
      · exact hnle.trans hnext.1
      · exact hnle.trans hnext.2
      · exact htail z (by simp [hz])

private theorem lowerHistoryExtreme_minimum (zs : List CertField) (z : CertField)
    (hz : z ∈ zs) : certFieldVal (lowerHistoryExtreme false zs) ≤ certFieldVal z := by
  rcases zs with _ | ⟨a, zs⟩
  · simp at hz
  · simpa [lowerHistoryExtreme] using fold_minimum a zs z hz

private theorem lowerHistoryExtreme_bound (maximum : Bool) (zs : List CertField) (z : CertField)
    (hz : z ∈ zs) :
    if maximum then certFieldVal z ≤ certFieldVal (lowerHistoryExtreme maximum zs)
    else certFieldVal (lowerHistoryExtreme maximum zs) ≤ certFieldVal z := by
  cases maximum
  · simpa using lowerHistoryExtreme_minimum zs z hz
  · simpa using lowerHistoryExtreme_maximum zs z hz

private theorem lowerHistoryExtreme_nonneg (maximum : Bool) (zs : List CertField)
    (hne : zs ≠ []) (h : ∀ z ∈ zs, 0 ≤ certFieldVal z) :
    0 ≤ certFieldVal (lowerHistoryExtreme maximum zs) :=
  h _ (lowerHistoryExtreme_mem maximum zs hne)


end M7Extreme14


open Freiman
namespace M7Goodness14

private theorem prefix_nonneg (w : List ℕ+) (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ prefixEval w z := by
  induction w with
  | nil => exact hz
  | cons a w ih =>
    simp only [prefixEval]
    positivity

private theorem tau_nonneg : 0 ≤ certFieldVal lowerHistoryTau := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  norm_num [certFieldVal, lowerHistoryTau]

private theorem endval_nonneg (C : LowerHistoryContext) (w : LowerPair)
    (upper side short : Bool) :
    0 ≤ certFieldVal (lowerHistoryEndVal C w upper side short) := by
  unfold lowerHistoryEndVal
  rw [lowerHistory_cf_value _ _ tau_nonneg]
  exact prefix_nonneg _ _ tau_nonneg

private theorem equal_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool)
    (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ lowerHistoryEqualCases C w upper) :
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2 := by
  by_cases hn : (lowerHistoryNatural C w upper false ||
      lowerHistoryNatural C w upper true) = true
  · simp only [lowerHistoryEqualCases, hn, ↓reduceIte,
      List.mem_singleton, Prod.mk.injEq] at hz
    rcases hz with ⟨rfl, rfl⟩
    exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩
  · dsimp only [lowerHistoryEqualCases] at hz
    rw [if_neg hn] at hz
    simp only [List.mem_flatMap, List.mem_map] at hz
    obtain ⟨⟨wide,norm⟩, _, shortened, _, heq⟩ := hz
    cases heq
    exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩

private theorem endpoint_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool)
    (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ lowerHistoryEndpointCases C w upper) :
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2 := by
  unfold lowerHistoryEndpointCases at hz
  split_ifs at hz with hp
  · exact equal_nonneg C w upper z cs hz
  · simp only [List.mem_flatMap, List.mem_map] at hz
    obtain ⟨⟨wide,norm⟩, _, ⟨v,bs⟩, hv, heq⟩ := hz
    cases heq
    split_ifs at hv
    · exact equal_nonneg _ _ _ _ _ hv
    · simp only [List.mem_singleton, Prod.mk.injEq] at hv
      rcases hv with ⟨rfl, rfl⟩
      exact ⟨endval_nonneg _ _ _ _ _, endval_nonneg _ _ _ _ _⟩

private theorem field_sub (x y : CertField) :
    certFieldVal (certFieldSub x y) = certFieldVal x - certFieldVal y := by
  simp only [certFieldVal, certFieldSub]
  push_cast
  ring

private theorem sign_nonneg (z : CertField) (b : Bool) :
    (0 ≤ (if b then -1 else 1 : ℤ) * lowerHistorySign z) ↔
      (0 ≤ (if b then -1 else 1 : ℝ) * certFieldVal z) := by
  have hsg := lowerHistory_sign_value z
  have hle : lowerHistorySign z ≤ 0 ↔ certFieldVal z ≤ 0 := by
    simpa only [not_lt] using not_congr hsg.2
  have hlt : lowerHistorySign z < 0 ↔ certFieldVal z < 0 := by
    simp only [lt_iff_le_and_ne, hle, ne_eq, hsg.1]
  have hge : 0 ≤ lowerHistorySign z ↔ 0 ≤ certFieldVal z := by
    simpa only [not_lt] using not_congr hlt
  cases b
  · simpa using hge
  · simpa using hle

private theorem value_mono (hg : LowerHistoryGreaterLaw) (base : LowerPair)
    (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (x y : CertField × CertField)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2)
    (h1 : 0 ≤ (if C.parity.1 then -1 else 1 : ℝ) *
      (certFieldVal x.1 - certFieldVal y.1))
    (h2 : 0 ≤ (if C.parity.2 then -1 else 1 : ℝ) *
      (certFieldVal x.2 - certFieldVal y.2)) :
    lowerHistoryValue base C y ≤ lowerHistoryValue base C x := by
  have hs1 : 0 ≤ (if C.parity.1 then -1 else 1 : ℤ) *
      lowerHistorySign (certFieldSub x.1 y.1) :=
    (sign_nonneg _ _).mpr (by simpa only [field_sub] using h1)
  have hs2 : 0 ≤ (if C.parity.2 then -1 else 1 : ℤ) *
      lowerHistorySign (certFieldSub x.2 y.2) :=
    (sign_nonneg _ _).mpr (by simpa only [field_sub] using h2)
  apply (hg base C hc x y hx hy).mp
  simp only [lowerHistoryGreater, hs1, hs2, and_self, ↓reduceIte,
    lowerHistoryComparisonHolds]

end M7Goodness14


open Freiman
namespace M7Goodness14

private theorem good_cross (base : LowerPair) (C : LowerHistoryContext)
    (hn : lowerNormalize base = base) (hb : lowerGood base) :
    (lowerHistoryEndpointReal base C ([2],[]) false ≤
      lowerHistoryEndpointReal base C ([1],[]) true) ∧
    (lowerHistoryEndpointReal base C ([1],[]) false ≤
      lowerHistoryEndpointReal base C ([2],[]) true) := by
  rcases hb with ⟨t, ht1, ht2⟩
  have h1 : lowerEndpoint (lowerHistoryAppend base ([1],[])) false ≤ t ∧
      t ≤ lowerEndpoint (lowerHistoryAppend base ([1],[])) true := by
    simpa only [lowerCover, Set.mem_Icc, lowerChild, hn, List.reverse_cons,
      List.reverse_nil, List.nil_append, lowerHistoryAppend] using ht1
  have h2 : lowerEndpoint (lowerHistoryAppend base ([2],[])) false ≤ t ∧
      t ≤ lowerEndpoint (lowerHistoryAppend base ([2],[])) true := by
    simpa only [lowerCover, Set.mem_Icc, lowerChild, hn, List.reverse_cons,
      List.reverse_nil, List.nil_append, lowerHistoryAppend] using ht2
  have h21 := h2.1.trans h1.2
  have h12 := h1.1.trans h2.2
  cases ho : lowerHistoryCommonOdd base C <;>
    simp only [lowerHistoryEndpointReal, ho, Bool.false_eq_true, ↓reduceIte,
      Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true, one_mul, neg_one_mul]
  · exact ⟨h21,h12⟩
  · exact ⟨neg_le_neg h12,neg_le_neg h21⟩

end M7Goodness14


open Freiman M7Extreme14
namespace M7Goodness14

private def hull (C : LowerHistoryContext) (w : LowerPair) (upper : Bool) : CertField × CertField :=
  let es := lowerHistoryEndpointCases C w upper
  (lowerHistoryExtreme (upper.xor C.parity.1) (es.map (fun z => z.1.1)),
   lowerHistoryExtreme (upper.xor C.parity.2) (es.map (fun z => z.1.2)))

private theorem hull_nonneg (C : LowerHistoryContext) (w : LowerPair) (upper : Bool)
    (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ lowerHistoryEndpointCases C w upper) :
    0 ≤ certFieldVal (hull C w upper).1 ∧
    0 ≤ certFieldVal (hull C w upper).2 := by
  have h1 : z.1 ∈ (lowerHistoryEndpointCases C w upper).map (fun z => z.1.1) :=
    List.mem_map.mpr ⟨(z,cs),hz,rfl⟩
  have h2 : z.2 ∈ (lowerHistoryEndpointCases C w upper).map (fun z => z.1.2) :=
    List.mem_map.mpr ⟨(z,cs),hz,rfl⟩
  constructor
  · apply lowerHistoryExtreme_nonneg _ _ (List.ne_nil_of_mem h1)
    intro a ha
    obtain ⟨⟨b,bs⟩,hb,rfl⟩ := List.mem_map.mp ha
    exact (endpoint_nonneg C w upper b bs hb).1
  · apply lowerHistoryExtreme_nonneg _ _ (List.ne_nil_of_mem h2)
    intro a ha
    obtain ⟨⟨b,bs⟩,hb,rfl⟩ := List.mem_map.mp ha
    exact (endpoint_nonneg C w upper b bs hb).2

private theorem upper_hull_ge (hg : LowerHistoryGreaterLaw) (base : LowerPair)
    (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (w : LowerPair) (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ lowerHistoryEndpointCases C w true) :
    lowerHistoryValue base C z ≤ lowerHistoryValue base C (hull C w true) := by
  have h1 : z.1 ∈ (lowerHistoryEndpointCases C w true).map (fun z => z.1.1) :=
    List.mem_map.mpr ⟨(z,cs),hz,rfl⟩
  have h2 : z.2 ∈ (lowerHistoryEndpointCases C w true).map (fun z => z.1.2) :=
    List.mem_map.mpr ⟨(z,cs),hz,rfl⟩
  apply value_mono hg base C hc (hull C w true) z
    (hull_nonneg C w true z cs hz) (endpoint_nonneg C w true z cs hz)
  · cases hp : C.parity.1
    · simpa [hull, hp] using sub_nonneg.mpr (lowerHistoryExtreme_maximum _ _ h1)
    · simpa [hull, hp] using sub_nonneg.mpr (lowerHistoryExtreme_minimum _ _ h1)
  · cases hp : C.parity.2
    · simpa [hull, hp] using sub_nonneg.mpr (lowerHistoryExtreme_maximum _ _ h2)
    · simpa [hull, hp] using sub_nonneg.mpr (lowerHistoryExtreme_minimum _ _ h2)

private theorem lower_hull_le (hg : LowerHistoryGreaterLaw) (base : LowerPair)
    (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (w : LowerPair) (z : CertField × CertField) (cs : List CertBound)
    (hz : (z,cs) ∈ lowerHistoryEndpointCases C w false) :
    lowerHistoryValue base C (hull C w false) ≤ lowerHistoryValue base C z := by
  have h1 : z.1 ∈ (lowerHistoryEndpointCases C w false).map (fun z => z.1.1) :=
    List.mem_map.mpr ⟨(z,cs),hz,rfl⟩
  have h2 : z.2 ∈ (lowerHistoryEndpointCases C w false).map (fun z => z.1.2) :=
    List.mem_map.mpr ⟨(z,cs),hz,rfl⟩
  apply value_mono hg base C hc z (hull C w false)
    (endpoint_nonneg C w false z cs hz) (hull_nonneg C w false z cs hz)
  · cases hp : C.parity.1
    · simpa [hull, hp] using sub_nonneg.mpr (lowerHistoryExtreme_minimum _ _ h1)
    · simpa [hull, hp] using sub_nonneg.mpr (lowerHistoryExtreme_maximum _ _ h1)
  · cases hp : C.parity.2
    · simpa [hull, hp] using sub_nonneg.mpr (lowerHistoryExtreme_minimum _ _ h2)
    · simpa [hull, hp] using sub_nonneg.mpr (lowerHistoryExtreme_maximum _ _ h2)

private def envelopeComparison (C : LowerHistoryContext) (u v : LowerPair) : LowerHistoryComparison :=
  lowerHistoryGreater C (hull C u true) (hull C v false)

private theorem envelope_comparison (hg : LowerHistoryGreaterLaw) (he : LowerHistoryEndpointLaw)
    (base : LowerPair) (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (u v : LowerPair)
    (huv : lowerHistoryEndpointReal base C v false ≤ lowerHistoryEndpointReal base C u true) :
    lowerHistoryComparisonHolds (envelopeComparison C u v)
      (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) := by
  obtain ⟨x,cx,hx,_,hex⟩ := he base C hc u true
  obtain ⟨y,cy,hy,_,hey⟩ := he base C hc v false
  apply (hg base C hc (hull C u true) (hull C v false)
    (hull_nonneg C u true x cx hx) (hull_nonneg C v false y cy hy)).mpr
  have hxy : lowerHistoryValue base C y ≤ lowerHistoryValue base C x := by
    simpa only [hex,hey] using huv
  exact (lower_hull_le hg base C hc v y cy hy).trans
    (hxy.trans (upper_hull_ge hg base C hc u x cx hx))

end M7Goodness14


open Freiman
namespace M7Goodness14

private def comparisonBounds : LowerHistoryComparison → Option (List CertBound)
  | .automatic => some []
  | .impossible => none
  | .bound b => some [b]

private theorem relaxed_unroll (C : LowerHistoryContext) :
    lowerHistoryRelaxedGoodness C =
      (comparisonBounds (envelopeComparison C ([1],[]) ([2],[]))).bind (fun bs =>
        (comparisonBounds (envelopeComparison C ([2],[]) ([1],[]))).map (fun cs => bs ++ cs)) := by
  unfold lowerHistoryRelaxedGoodness envelopeComparison hull comparisonBounds
  simp only [Bool.true_xor, Bool.false_xor]
  split <;> split <;> simp_all [List.forIn_cons, List.forIn_nil]

private theorem collect_bounds (base : LowerPair) (g : LowerHistoryComparison)
    (hg : lowerHistoryComparisonHolds g (lowerRatio base.1) (lowerRatio base.2) (lowerScale base)) :
    ∃ bs, comparisonBounds g = some bs ∧ lowerHistoryAtBase base bs := by
  cases g with
  | automatic => exact ⟨[], rfl, by simp [lowerHistoryAtBase, lowerHistoryConditions]⟩
  | impossible => exact hg.elim
  | bound b => exact ⟨[b], rfl, by simpa [lowerHistoryAtBase, lowerHistoryConditions, lowerHistoryComparisonHolds] using hg⟩

private theorem goodness_from_endpoints (hg : LowerHistoryGreaterLaw) (he : LowerHistoryEndpointLaw) :
    LowerHistoryGoodnessLaw := by
  intro base C hc hn hb
  have hcross := good_cross base C hn hb
  have h1 := envelope_comparison hg he base C hc ([1],[]) ([2],[]) hcross.1
  have h2 := envelope_comparison hg he base C hc ([2],[]) ([1],[]) hcross.2
  obtain ⟨bs,hbs,hbsval⟩ := collect_bounds base _ h1
  obtain ⟨cs,hcs,hcsval⟩ := collect_bounds base _ h2
  refine ⟨bs++cs, ?_, ?_⟩
  · rw [relaxed_unroll, hbs]
    simp only [Option.bind_some, hcs, Option.map_some]
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hbsval b hb
    · exact hcsval b hb

end M7Goodness14

theorem solution (hg : LowerHistoryGreaterLaw) (he : LowerHistoryEndpointLaw) :
    LowerHistoryGoodnessLaw := by
  exact M7Goodness14.goodness_from_endpoints hg he

#print axioms solution
