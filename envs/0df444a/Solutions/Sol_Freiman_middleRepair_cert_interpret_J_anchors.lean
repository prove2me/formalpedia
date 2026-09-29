-- Prove2me | solution 1 for Freiman.middleRepair_cert_interpret_J_anchors
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:55:28.941665+00:00
-- url     : https://prove2.me/submissions/e3243440-333a-4441-b372-fcfe535dcff3

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
      0 < u.length+v.length → middleRegular (middleRepairChild c u v) ∧ middleRepairProper c (middleRepairChild c u v)) → (∀ c : MiddleCore, middleRegular c → (middleBounds c).1 ≤ (middleBounds c).2) → ∀ (c : MiddleCore) (f : Fin 9), middleRepairCertDomain c f.val → middleRepairCertActualFamily c f.val → middleEssentialJ (middleCertRow f.val)=true → middleRepairJAnchors c (middleRepairRowChildren c (middleCertRow f.val)) := by
  intro _hcriterion hchild horder c f hd ha hj
  have hc := hd.1
  fin_cases f
  · simp [middleCertRow, middleEssentialJ] at hj
  · simp [middleCertRow, middleEssentialJ] at hj
  · simp [middleCertRow, middleEssentialJ] at hj
  · simp [middleCertRow, middleEssentialJ] at hj
  · have ho1 := child_order hchild horder c hc [3,3] [3,3] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho2 := child_order hchild horder c hc [3] [2] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have hlo := ha ⟨.outerLow,([],[]),false,([3],[3]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hhi := ha ⟨.outerHigh,([],[1]),true,([],[]),true,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hfor := ha ⟨.anchor true,([3,3],[3,3]),true,([3],[2]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hback := ha ⟨.anchor false,([3],[2]),true,([3,3],[3,3]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have ha1 := spec_inequality c _ ([3,3],[3,3]) ([3],[2]) true false rfl hfor
    have ha2 := spec_inequality c _ ([3],[2]) ([3,3],[3,3]) true false rfl hback
    have hl := spec_inequality c _ ([],[]) ([3],[3]) false false rfl hlo
    have hh := spec_inequality c _ ([],[1]) ([],[]) true true rfl hhi
    by_cases hp : (middleNormalized c).left.length % 2 = 0
    · simp only [hp, ↓reduceIte, bounds_child_empty] at ha1 ha2 hl hh
      refine ⟨⟨middleRepairChild c [3] [2], by simp [middleRepairRowChildren, middleCertRow], ?_⟩, Or.inl ⟨?_, ?_⟩⟩
      · simpa [middleRepairJ] using covers_overlap _ _ ho1 ho2 ha2 ha1
      · simpa [middleRepairJ] using hl
      · exact ⟨middleRepairChild c [] [1], by simp [middleRepairRowChildren, middleCertRow], hh⟩
    · simp only [hp, ↓reduceIte, bounds_child_empty, neg_le_neg_iff] at ha1 ha2 hl hh
      refine ⟨⟨middleRepairChild c [3] [2], by simp [middleRepairRowChildren, middleCertRow], ?_⟩, Or.inr ⟨?_, ?_⟩⟩
      · simpa [middleRepairJ] using covers_overlap _ _ ho1 ho2 ha1 ha2
      · simpa [middleRepairJ] using hl
      · exact ⟨middleRepairChild c [] [1], by simp [middleRepairRowChildren, middleCertRow], hh⟩
  · simp [middleCertRow, middleEssentialJ] at hj
  · simp [middleCertRow, middleEssentialJ] at hj
  · simp [middleCertRow, middleEssentialJ] at hj
  · have ho1 := child_order hchild horder c hc [3,3] [3,3] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have ho2 := child_order hchild horder c hc [3] [2] (by simp [middleDigits123]) (by simp [middleDigits123]) (by simp)
    have hlo := ha ⟨.outerLow,([],[]),false,([3],[3]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hhi := ha ⟨.outerHigh,([1],[]),true,([],[]),true,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hfor := ha ⟨.anchor true,([3,3],[3,3]),true,([3],[2]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have hback := ha ⟨.anchor false,([3],[2]),true,([3,3],[3,3]),false,[]⟩ (by simp [middleCertSpecs, middleCertChildren])
    have ha1 := spec_inequality c _ ([3,3],[3,3]) ([3],[2]) true false rfl hfor
    have ha2 := spec_inequality c _ ([3],[2]) ([3,3],[3,3]) true false rfl hback
    have hl := spec_inequality c _ ([],[]) ([3],[3]) false false rfl hlo
    have hh := spec_inequality c _ ([1],[]) ([],[]) true true rfl hhi
    by_cases hp : (middleNormalized c).left.length % 2 = 0
    · simp only [hp, ↓reduceIte, bounds_child_empty] at ha1 ha2 hl hh
      refine ⟨⟨middleRepairChild c [3] [2], by simp [middleRepairRowChildren, middleCertRow], ?_⟩, Or.inl ⟨?_, ?_⟩⟩
      · simpa [middleRepairJ] using covers_overlap _ _ ho1 ho2 ha2 ha1
      · simpa [middleRepairJ] using hl
      · exact ⟨middleRepairChild c [1] [], by simp [middleRepairRowChildren, middleCertRow], hh⟩
    · simp only [hp, ↓reduceIte, bounds_child_empty, neg_le_neg_iff] at ha1 ha2 hl hh
      refine ⟨⟨middleRepairChild c [3] [2], by simp [middleRepairRowChildren, middleCertRow], ?_⟩, Or.inr ⟨?_, ?_⟩⟩
      · simpa [middleRepairJ] using covers_overlap _ _ ho1 ho2 ha1 ha2
      · simpa [middleRepairJ] using hl
      · exact ⟨middleRepairChild c [1] [], by simp [middleRepairRowChildren, middleCertRow], hh⟩

#print axioms solution
