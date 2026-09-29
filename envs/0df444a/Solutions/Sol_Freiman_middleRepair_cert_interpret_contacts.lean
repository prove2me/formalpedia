-- Prove2me | solution 1 for Freiman.middleRepair_cert_interpret_contacts
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:54:43.12082+00:00
-- url     : https://prove2.me/submissions/18f28cd2-b736-48be-b54d-eeecd87fdf10

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

set_option linter.unusedSimpArgs false

private theorem normalized_idem (c : MiddleCore) : middleNormalized (middleNormalized c) = middleNormalized c := by
  unfold middleNormalized
  split_ifs <;> first | rfl | (simp_all only [not_le]; order)

private theorem bounds_normalized (c : MiddleCore) : middleBounds (middleNormalized c) = middleBounds c := by
  simp only [middleBounds, normalized_idem]

private theorem bounds_child_empty (c : MiddleCore) :
    middleBounds (middleRepairChild c [] []) = middleBounds c := by
  simp only [middleRepairChild, middleRepairRawChild, List.append_nil,
    bounds_normalized]
  exact bounds_normalized c

private theorem endpoint_false (c : MiddleCore) (w : LowerPair) (upper : Bool) :
    middleRepairCertEndpoint c w upper false =
      if (middleNormalized c).left.length % 2 = 0 then
        (if upper then (middleBounds (middleRepairChild c w.1 w.2)).2
          else (middleBounds (middleRepairChild c w.1 w.2)).1)
      else -(if upper then (middleBounds (middleRepairChild c w.1 w.2)).1
          else (middleBounds (middleRepairChild c w.1 w.2)).2) := by
  simp only [middleRepairCertEndpoint, middleRepairAct, Bool.false_eq_true,
    ↓reduceIte, middleRepairChild, middleRepairRawChild, bounds_normalized]

private theorem spec_inequality (c : MiddleCore) (role : MiddleCertRole)
    (w v : LowerPair) (a b : Bool)
    (hi : middleRepairCertIncoming role = false)
    (hs : middleRepairCertSpecHolds c ⟨role,w,a,v,b,[]⟩) :
    (if (middleNormalized c).left.length % 2 = 0 then
        (if b then (middleBounds (middleRepairChild c v.1 v.2)).2
          else (middleBounds (middleRepairChild c v.1 v.2)).1)
      else -(if b then (middleBounds (middleRepairChild c v.1 v.2)).1
          else (middleBounds (middleRepairChild c v.1 v.2)).2)) ≤
    (if (middleNormalized c).left.length % 2 = 0 then
        (if a then (middleBounds (middleRepairChild c w.1 w.2)).2
          else (middleBounds (middleRepairChild c w.1 w.2)).1)
      else -(if a then (middleBounds (middleRepairChild c w.1 w.2)).1
          else (middleBounds (middleRepairChild c w.1 w.2)).2)) := by
  have he := hs (by simp [middleCertHolds])
  change middleRepairCertEndpoint c v b (middleRepairCertIncoming role) ≤
    middleRepairCertEndpoint c w a (middleRepairCertIncoming role) at he
  simpa only [hi, endpoint_false] using he

private theorem covers_overlap (d e : MiddleCore)
    (hd : (middleBounds d).1 ≤ (middleBounds d).2)
    (he : (middleBounds e).1 ≤ (middleBounds e).2)
    (hde : (middleBounds d).1 ≤ (middleBounds e).2)
    (hed : (middleBounds e).1 ≤ (middleBounds d).2) :
    (middleCover d ∩ middleCover e).Nonempty := by
  refine ⟨max (middleBounds d).1 (middleBounds e).1, ?_⟩
  exact ⟨⟨le_max_left _ _, max_le hd hed⟩, ⟨le_max_right _ _, max_le hde he⟩⟩

private theorem contact_from_specs (c : MiddleCore) (k : ℕ) (w v : LowerPair)
    (hd : (middleBounds (middleRepairChild c w.1 w.2)).1 ≤
      (middleBounds (middleRepairChild c w.1 w.2)).2)
    (he : (middleBounds (middleRepairChild c v.1 v.2)).1 ≤
      (middleBounds (middleRepairChild c v.1 v.2)).2)
    (hfor : middleRepairCertSpecHolds c ⟨.contact k true,w,true,v,false,[]⟩)
    (hback : middleRepairCertSpecHolds c ⟨.contact k false,v,true,w,false,[]⟩) :
    (middleCover (middleRepairChild c w.1 w.2) ∩
      middleCover (middleRepairChild c v.1 v.2)).Nonempty := by
  have h1 := spec_inequality c _ w v true false rfl hfor
  have h2 := spec_inequality c _ v w true false rfl hback
  by_cases hp : (middleNormalized c).left.length % 2 = 0
  · simp only [hp, ↓reduceIte, Bool.true_eq_false] at h1 h2
    exact covers_overlap _ _ hd he h2 h1
  · simp only [hp, ↓reduceIte, Bool.true_eq_false, neg_le_neg_iff] at h1 h2
    exact covers_overlap _ _ hd he h1 h2

private theorem child_order
    (hchild : ∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c →
      middleDigits123 u → middleDigits123 v → 0 < u.length+v.length →
      middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v))
    (horder : ∀ c : MiddleCore, middleRegular c → (middleBounds c).1 ≤ (middleBounds c).2)
    (c : MiddleCore) (hc : middleRegular c) (u v : List ℕ+)
    (hu : middleDigits123 u) (hv : middleDigits123 v) (hl : 0 < u.length+v.length) :
    (middleBounds (middleRepairChild c u v)).1 ≤ (middleBounds (middleRepairChild c u v)).2 :=
  horder _ (hchild c u v hc hu hv hl).1

theorem solution :
    (∀ c : MiddleCore, middleRegular c → (middleRepairGood c ↔ (if (middleNormalized c).left.length%2=0 then (middleBounds (middleRepairChild c [1] [])).1 ≤ (middleBounds (middleRepairChild c [2] [])).2 else (middleBounds (middleRepairChild c [2] [])).1 ≤ (middleBounds (middleRepairChild c [1] [])).2))) → (∀ (c : MiddleCore) (u v : List ℕ+), middleRegular c → middleDigits123 u → middleDigits123 v →
      0 < u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v)) → (∀ c : MiddleCore, middleRegular c → (middleBounds c).1 ≤ (middleBounds c).2) → ∀ (c : MiddleCore) (f : Fin 9), middleRepairCertDomain c f.val → middleRepairCertActualFamily c f.val → middleContacts (middleRepairRowChildren c (middleCertRow f.val)) := by
  intro _hcriterion hchild horder c f hd ha
  have hc := hd.1
  fin_cases f
  · have ho0 := child_order hchild horder c hc [] [1] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho1 := child_order hchild horder c hc [1] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have hf0 := ha ⟨.contact 0 true,([],[1]),true,([1],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb0 := ha ⟨.contact 0 false,([1],[]),true,([],[1]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov0 := contact_from_specs c 0 ([],[1]) ([1],[]) ho0 ho1 hf0 hb0
    constructor
    · intro d hm
      simp only [middleCertRow, middleRepairRowChildren, middleRepairJ, List.replicate_succ, List.replicate_zero, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact ⟨(middleBounds (middleRepairChild c [] [1])).1, le_rfl, ho0⟩
      · exact ⟨(middleBounds (middleRepairChild c [1] [])).1, le_rfl, ho1⟩
    · intro j hj
      simp only [middleCertRow, middleRepairRowChildren, List.length_cons, List.length_nil] at hj
      have cases_j : j = 0 := by omega
      rcases cases_j with rfl
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov0
  · have ho0 := child_order hchild horder c hc [3] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho1 := child_order hchild horder c hc [2] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho2 := child_order hchild horder c hc [1] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have hf0 := ha ⟨.contact 0 true,([3],[]),true,([2],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb0 := ha ⟨.contact 0 false,([2],[]),true,([3],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov0 := contact_from_specs c 0 ([3],[]) ([2],[]) ho0 ho1 hf0 hb0
    have hf1 := ha ⟨.contact 1 true,([2],[]),true,([1],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb1 := ha ⟨.contact 1 false,([1],[]),true,([2],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov1 := contact_from_specs c 1 ([2],[]) ([1],[]) ho1 ho2 hf1 hb1
    constructor
    · intro d hm
      simp only [middleCertRow, middleRepairRowChildren, middleRepairJ, List.replicate_succ, List.replicate_zero, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨(middleBounds (middleRepairChild c [3] [])).1, le_rfl, ho0⟩
      · exact ⟨(middleBounds (middleRepairChild c [2] [])).1, le_rfl, ho1⟩
      · exact ⟨(middleBounds (middleRepairChild c [1] [])).1, le_rfl, ho2⟩
    · intro j hj
      simp only [middleCertRow, middleRepairRowChildren, List.length_cons, List.length_nil] at hj
      have cases_j : j = 0 ∨ j = 1 := by omega
      rcases cases_j with rfl | rfl
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov0
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov1
  · have ho0 := child_order hchild horder c hc [3] [1] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho1 := child_order hchild horder c hc [2] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho2 := child_order hchild horder c hc [1] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have hf0 := ha ⟨.contact 0 true,([3],[1]),true,([2],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb0 := ha ⟨.contact 0 false,([2],[]),true,([3],[1]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov0 := contact_from_specs c 0 ([3],[1]) ([2],[]) ho0 ho1 hf0 hb0
    have hf1 := ha ⟨.contact 1 true,([2],[]),true,([1],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb1 := ha ⟨.contact 1 false,([1],[]),true,([2],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov1 := contact_from_specs c 1 ([2],[]) ([1],[]) ho1 ho2 hf1 hb1
    constructor
    · intro d hm
      simp only [middleCertRow, middleRepairRowChildren, middleRepairJ, List.replicate_succ, List.replicate_zero, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨(middleBounds (middleRepairChild c [3] [1])).1, le_rfl, ho0⟩
      · exact ⟨(middleBounds (middleRepairChild c [2] [])).1, le_rfl, ho1⟩
      · exact ⟨(middleBounds (middleRepairChild c [1] [])).1, le_rfl, ho2⟩
    · intro j hj
      simp only [middleCertRow, middleRepairRowChildren, List.length_cons, List.length_nil] at hj
      have cases_j : j = 0 ∨ j = 1 := by omega
      rcases cases_j with rfl | rfl
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov0
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov1
  · have ho0 := child_order hchild horder c hc [3] [2] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho1 := child_order hchild horder c hc [2] [3] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho2 := child_order hchild horder c hc [2] [2] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho3 := child_order hchild horder c hc [] [1] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have hf0 := ha ⟨.contact 0 true,([3],[2]),true,([2],[3]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb0 := ha ⟨.contact 0 false,([2],[3]),true,([3],[2]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov0 := contact_from_specs c 0 ([3],[2]) ([2],[3]) ho0 ho1 hf0 hb0
    have hf1 := ha ⟨.contact 1 true,([2],[3]),true,([2],[2]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb1 := ha ⟨.contact 1 false,([2],[2]),true,([2],[3]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov1 := contact_from_specs c 1 ([2],[3]) ([2],[2]) ho1 ho2 hf1 hb1
    have hf2 := ha ⟨.contact 2 true,([2],[2]),true,([],[1]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb2 := ha ⟨.contact 2 false,([],[1]),true,([2],[2]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov2 := contact_from_specs c 2 ([2],[2]) ([],[1]) ho2 ho3 hf2 hb2
    constructor
    · intro d hm
      simp only [middleCertRow, middleRepairRowChildren, middleRepairJ, List.replicate_succ, List.replicate_zero, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · exact ⟨(middleBounds (middleRepairChild c [3] [2])).1, le_rfl, ho0⟩
      · exact ⟨(middleBounds (middleRepairChild c [2] [3])).1, le_rfl, ho1⟩
      · exact ⟨(middleBounds (middleRepairChild c [2] [2])).1, le_rfl, ho2⟩
      · exact ⟨(middleBounds (middleRepairChild c [] [1])).1, le_rfl, ho3⟩
    · intro j hj
      simp only [middleCertRow, middleRepairRowChildren, List.length_cons, List.length_nil] at hj
      have cases_j : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases cases_j with rfl | rfl | rfl
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov0
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov1
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov2
  · have ho0 := child_order hchild horder c hc [3] [2] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho1 := child_order hchild horder c hc [2] [3] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho2 := child_order hchild horder c hc [2] [2] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho3 := child_order hchild horder c hc [] [1] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have hf0 := ha ⟨.contact 0 true,([3],[2]),true,([2],[3]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb0 := ha ⟨.contact 0 false,([2],[3]),true,([3],[2]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov0 := contact_from_specs c 0 ([3],[2]) ([2],[3]) ho0 ho1 hf0 hb0
    have hf1 := ha ⟨.contact 1 true,([2],[3]),true,([2],[2]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb1 := ha ⟨.contact 1 false,([2],[2]),true,([2],[3]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov1 := contact_from_specs c 1 ([2],[3]) ([2],[2]) ho1 ho2 hf1 hb1
    have hf2 := ha ⟨.contact 2 true,([2],[2]),true,([],[1]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb2 := ha ⟨.contact 2 false,([],[1]),true,([2],[2]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov2 := contact_from_specs c 2 ([2],[2]) ([],[1]) ho2 ho3 hf2 hb2
    constructor
    · intro d hm
      simp only [middleCertRow, middleRepairRowChildren, middleRepairJ, List.replicate_succ, List.replicate_zero, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · exact ⟨(middleBounds (middleRepairChild c [3] [2])).1, le_rfl, ho0⟩
      · exact ⟨(middleBounds (middleRepairChild c [2] [3])).1, le_rfl, ho1⟩
      · exact ⟨(middleBounds (middleRepairChild c [2] [2])).1, le_rfl, ho2⟩
      · exact ⟨(middleBounds (middleRepairChild c [] [1])).1, le_rfl, ho3⟩
    · intro j hj
      simp only [middleCertRow, middleRepairRowChildren, List.length_cons, List.length_nil] at hj
      have cases_j : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases cases_j with rfl | rfl | rfl
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov0
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov1
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov2
  · have ho0 := child_order hchild horder c hc [3] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho1 := child_order hchild horder c hc [2] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho2 := child_order hchild horder c hc [1] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have hf0 := ha ⟨.contact 0 true,([3],[]),true,([2],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb0 := ha ⟨.contact 0 false,([2],[]),true,([3],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov0 := contact_from_specs c 0 ([3],[]) ([2],[]) ho0 ho1 hf0 hb0
    have hf1 := ha ⟨.contact 1 true,([2],[]),true,([1],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb1 := ha ⟨.contact 1 false,([1],[]),true,([2],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov1 := contact_from_specs c 1 ([2],[]) ([1],[]) ho1 ho2 hf1 hb1
    constructor
    · intro d hm
      simp only [middleCertRow, middleRepairRowChildren, middleRepairJ, List.replicate_succ, List.replicate_zero, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨(middleBounds (middleRepairChild c [3] [])).1, le_rfl, ho0⟩
      · exact ⟨(middleBounds (middleRepairChild c [2] [])).1, le_rfl, ho1⟩
      · exact ⟨(middleBounds (middleRepairChild c [1] [])).1, le_rfl, ho2⟩
    · intro j hj
      simp only [middleCertRow, middleRepairRowChildren, List.length_cons, List.length_nil] at hj
      have cases_j : j = 0 ∨ j = 1 := by omega
      rcases cases_j with rfl | rfl
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov0
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov1
  · have ho0 := child_order hchild horder c hc [3] [3] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho1 := child_order hchild horder c hc [3] [2] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho2 := child_order hchild horder c hc [2] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho3 := child_order hchild horder c hc [1] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have hf0 := ha ⟨.contact 0 true,([3],[3]),true,([3],[2]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb0 := ha ⟨.contact 0 false,([3],[2]),true,([3],[3]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov0 := contact_from_specs c 0 ([3],[3]) ([3],[2]) ho0 ho1 hf0 hb0
    have hf1 := ha ⟨.contact 1 true,([3],[2]),true,([2],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb1 := ha ⟨.contact 1 false,([2],[]),true,([3],[2]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov1 := contact_from_specs c 1 ([3],[2]) ([2],[]) ho1 ho2 hf1 hb1
    have hf2 := ha ⟨.contact 2 true,([2],[]),true,([1],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb2 := ha ⟨.contact 2 false,([1],[]),true,([2],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov2 := contact_from_specs c 2 ([2],[]) ([1],[]) ho2 ho3 hf2 hb2
    constructor
    · intro d hm
      simp only [middleCertRow, middleRepairRowChildren, middleRepairJ, List.replicate_succ, List.replicate_zero, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · exact ⟨(middleBounds (middleRepairChild c [3] [3])).1, le_rfl, ho0⟩
      · exact ⟨(middleBounds (middleRepairChild c [3] [2])).1, le_rfl, ho1⟩
      · exact ⟨(middleBounds (middleRepairChild c [2] [])).1, le_rfl, ho2⟩
      · exact ⟨(middleBounds (middleRepairChild c [1] [])).1, le_rfl, ho3⟩
    · intro j hj
      simp only [middleCertRow, middleRepairRowChildren, List.length_cons, List.length_nil] at hj
      have cases_j : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases cases_j with rfl | rfl | rfl
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov0
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov1
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov2
  · have ho0 := child_order hchild horder c hc [3] [2] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho1 := child_order hchild horder c hc [2] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho2 := child_order hchild horder c hc [1] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have hf0 := ha ⟨.contact 0 true,([3],[2]),true,([2],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb0 := ha ⟨.contact 0 false,([2],[]),true,([3],[2]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov0 := contact_from_specs c 0 ([3],[2]) ([2],[]) ho0 ho1 hf0 hb0
    have hf1 := ha ⟨.contact 1 true,([2],[]),true,([1],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb1 := ha ⟨.contact 1 false,([1],[]),true,([2],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov1 := contact_from_specs c 1 ([2],[]) ([1],[]) ho1 ho2 hf1 hb1
    constructor
    · intro d hm
      simp only [middleCertRow, middleRepairRowChildren, middleRepairJ, List.replicate_succ, List.replicate_zero, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨(middleBounds (middleRepairChild c [3] [2])).1, le_rfl, ho0⟩
      · exact ⟨(middleBounds (middleRepairChild c [2] [])).1, le_rfl, ho1⟩
      · exact ⟨(middleBounds (middleRepairChild c [1] [])).1, le_rfl, ho2⟩
    · intro j hj
      simp only [middleCertRow, middleRepairRowChildren, List.length_cons, List.length_nil] at hj
      have cases_j : j = 0 ∨ j = 1 := by omega
      rcases cases_j with rfl | rfl
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov0
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov1
  · have ho0 := child_order hchild horder c hc [3] [2] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho1 := child_order hchild horder c hc [2] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho2 := child_order hchild horder c hc [1] [] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have hf0 := ha ⟨.contact 0 true,([3],[2]),true,([2],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb0 := ha ⟨.contact 0 false,([2],[]),true,([3],[2]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov0 := contact_from_specs c 0 ([3],[2]) ([2],[]) ho0 ho1 hf0 hb0
    have hf1 := ha ⟨.contact 1 true,([2],[]),true,([1],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hb1 := ha ⟨.contact 1 false,([1],[]),true,([2],[]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hov1 := contact_from_specs c 1 ([2],[]) ([1],[]) ho1 ho2 hf1 hb1
    constructor
    · intro d hm
      simp only [middleCertRow, middleRepairRowChildren, middleRepairJ, List.replicate_succ, List.replicate_zero, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · exact ⟨(middleBounds (middleRepairChild c [3] [2])).1, le_rfl, ho0⟩
      · exact ⟨(middleBounds (middleRepairChild c [2] [])).1, le_rfl, ho1⟩
      · exact ⟨(middleBounds (middleRepairChild c [1] [])).1, le_rfl, ho2⟩
    · intro j hj
      simp only [middleCertRow, middleRepairRowChildren, List.length_cons, List.length_nil] at hj
      have cases_j : j = 0 ∨ j = 1 := by omega
      rcases cases_j with rfl | rfl
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov0
      · simpa [middleCertRow, middleRepairRowChildren, middleRepairJ, List.getD] using hov1

#print axioms solution
