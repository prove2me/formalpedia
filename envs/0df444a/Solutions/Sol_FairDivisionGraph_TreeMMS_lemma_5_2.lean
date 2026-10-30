-- Prove2me | solution 1 for FairDivisionGraph.TreeMMS.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T18:51:00.075309+00:00
-- url     : https://prove2.me/submissions/99151917-5bd3-4473-b9f8-ec03d748cc3a

import Definitions.Def_FairDivisionGraph_TreeMMS_Encoding
import Definitions.Def_FairDivisionGraph_TreeMMS_Algorithm
import Mathlib
set_option autoImplicit false
namespace Queelius.TreeMMS
open FairDivisionGraph.TreeMMS

lemma partition_lower_iff {m k : ℕ} (u : Fin m → ℝ) (P : Fin k → Finset (Fin m))
    (hk : 0 < k) (q : ℝ) : q ≤ partitionValue u P ↔ ∀ j,q ≤ value u (P j) := by
  classical
  let vals := Finset.univ.image (fun j => value u (P j))
  have hv : vals.Nonempty := ⟨value u (P ⟨0,hk⟩),Finset.mem_image.mpr ⟨⟨0,hk⟩,Finset.mem_univ _,rfl⟩⟩
  change q ≤ (if h : vals.Nonempty then vals.min' h else 0) ↔ _
  rw [dif_pos hv,Finset.le_min'_iff]
  constructor
  · intro h j
    exact h _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  · intro h x hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    exact h j

lemma mms_attained {m k : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (u : Fin m → ℝ) (hp : (partitions G V k).Nonempty) :
    ∃ P : Fin k → Finset (Fin m),ConnectedPartition G V P ∧ mms G V k u=partitionValue u P := by
  classical
  let vals := (partitions G V k).image (partitionValue u)
  have hv : vals.Nonempty := hp.image _
  have hm := Finset.max'_mem vals hv
  obtain ⟨P,hP,he⟩ := Finset.mem_image.mp hm
  refine ⟨P,(Finset.mem_filter.mp hP).2,?_⟩
  change (if h : vals.Nonempty then vals.max' h else 0)=partitionValue u P
  rw [dif_pos hv]
  exact he.symm

lemma partition_le_mms {m k : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (u : Fin m → ℝ) (P : Fin k → Finset (Fin m)) (hP : ConnectedPartition G V P) :
    partitionValue u P ≤ mms G V k u := by
  classical
  let vals := (partitions G V k).image (partitionValue u)
  have hm : partitionValue u P ∈ vals := Finset.mem_image.mpr ⟨P,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hP⟩,rfl⟩
  change _ ≤ if h : vals.Nonempty then vals.max' h else 0
  rw [dif_pos ⟨_,hm⟩]
  exact Finset.le_max' vals _ hm

lemma mms_threshold_iff {m k : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (u : Fin m → ℝ) (hk : 0 < k) (hp : (partitions G V k).Nonempty) (q : ℝ) :
    q ≤ mms G V k u ↔ ∃ P : Fin k → Finset (Fin m),ConnectedPartition G V P ∧ ∀ j,q ≤ value u (P j) := by
  constructor
  · intro hq
    obtain ⟨P,hP,he⟩ := mms_attained G V u hp
    exact ⟨P,hP,(partition_lower_iff u P hk q).mp (by rwa [← he])⟩
  · rintro ⟨P,hP,hq⟩
    exact ((partition_lower_iff u P hk q).mpr hq).trans (partition_le_mms G V u P hP)

lemma finite_rational_threshold_bridge {I P : Type*} [Fintype I] [Fintype P] [Nonempty P]
    (a : I → ℝ) (v : P → I → ℝ) (B : P → Prop)
    (hsolve : ∀ q : I → ℚ,(∀ i,(q i:ℝ) ≤ a i) → ∃ p,B p ∧ ∀ i,(q i:ℝ) ≤ v p i) :
    ∃ p,B p ∧ ∀ i,a i ≤ v p i := by
  classical
  by_contra hnot
  have hbad : ∀ p,B p → ∃ i,v p i < a i := by
    intro p hp
    by_contra hn
    apply hnot
    exact ⟨p,hp,fun i => le_of_not_gt (fun hi => hn ⟨i,hi⟩)⟩
  have hbase : ∀ i,∃ q : ℚ,(q:ℝ)<a i := fun i => exists_rat_lt (a i)
  choose q0 hq0 using hbase
  have hsep : ∀ p,∃ q : I → ℚ,(∀ i,(q i:ℝ) ≤ a i) ∧ (B p → ¬∀ i,(q i:ℝ) ≤ v p i) := by
    intro p
    by_cases hp : B p
    · obtain ⟨i,hi⟩ := hbad p hp
      obtain ⟨q,hql,hqu⟩ := exists_rat_btwn hi
      refine ⟨fun j => if j=i then q else q0 j,?_,?_⟩
      · intro j
        by_cases hj : j=i
        · subst j;simpa using hqu.le
        · simpa [hj] using (hq0 j).le
      · intro hp hall
        have hh := hall i
        simp only [ite_true] at hh
        exact (not_le_of_gt hql) hh
    · exact ⟨q0,fun i => (hq0 i).le,fun hb => (hp hb).elim⟩
  choose qs hqs hfail using hsep
  have hN : (Finset.univ : Finset P).Nonempty := Finset.univ_nonempty
  let q : I → ℚ := fun i => Finset.univ.sup' hN (fun p => qs p i)
  have hq : ∀ i,(q i:ℝ) ≤ a i := by
    intro i
    obtain ⟨p,hp,he⟩ := (Finset.univ : Finset P).exists_mem_eq_sup' hN (fun p => qs p i)
    change ((Finset.univ.sup' hN (fun p => qs p i):ℚ):ℝ) ≤ a i
    rw [he]
    exact hqs p i
  obtain ⟨p,hp,hout⟩ := hsolve q hq
  apply hfail p hp
  intro i
  have hle : qs p i ≤ q i := Finset.le_sup' (fun p => qs p i) (Finset.mem_univ p)
  have hr : (qs p i:ℝ) ≤ (q i:ℝ) := by exact_mod_cast hle
  exact hr.trans (hout i)

lemma rational_thresholds_imply_mms {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (h : ∀ q : Fin n → ℚ,(∀ i,(q i:ℝ) ≤ mms G Finset.univ n (u i)) →
      ∃ π,Valid G π ∧ ∀ i,(q i:ℝ) ≤ value (u i) (π i)) : ∃ π,IsMMS G u π := by
  exact finite_rational_threshold_bridge (fun i => mms G Finset.univ n (u i))
    (fun π i => value (u i) (π i)) (Valid G) h

lemma threshold_existence_bridge
    (h : ∀ (m n : ℕ) (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
      (q : Fin n → ℚ),IsCFD u → G.IsTree →
      (∀ i,(q i:ℝ) ≤ mms G Finset.univ n (u i)) →
      ∃ π,Valid G π ∧ ∀ i,(q i:ℝ) ≤ value (u i) (π i)) :
    ∀ (m n : ℕ) (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ),
      IsCFD u → G.IsTree → ∃ π,IsMMS G u π := by
  intro m n G u hu hG
  exact rational_thresholds_imply_mms G u (fun q hq => h m n G u q hu hG hq)

lemma empty_valid {m n : ℕ} (G : SimpleGraph (Fin m)) : Valid G (fun _ : Fin n => ∅) := by
  constructor
  · intro i;exact Or.inl rfl
  · intro i j hij;simp

lemma nonpositive_thresholds {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (hq : ∀ i,q i ≤ 0) :
    ∃ π,Valid G π ∧ ∀ i,(q i:ℝ) ≤ value (u i) (π i) := by
  refine ⟨fun _ => ∅,empty_valid G,?_⟩
  intro i
  simp only [value,Finset.sum_empty]
  exact_mod_cast hq i

lemma value_rat_cast {m : ℕ} (u : Fin m → ℚ) (S : Finset (Fin m)) :
    value (fun v => (u v:ℝ)) S=((∑ v ∈ S,u v : ℚ):ℝ) := by
  simp only [value,Rat.cast_sum]

lemma partition_value_rational {m k : ℕ} (u : Fin m → ℚ) (P : Fin k → Finset (Fin m)) :
    ∃ r : ℚ,(r:ℝ)=partitionValue (fun v => (u v:ℝ)) P := by
  classical
  let vals := Finset.univ.image (fun j => value (fun v => (u v:ℝ)) (P j))
  by_cases hv : vals.Nonempty
  · have hm := Finset.min'_mem vals hv
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hm
    refine ⟨∑ v ∈ P j,u v,?_⟩
    rw [← value_rat_cast]
    change _=(if h : vals.Nonempty then vals.min' h else 0)
    rw [dif_pos hv]
    exact he
  · refine ⟨0,?_⟩
    rw [Rat.cast_zero]
    change (0:ℝ)=(if h : vals.Nonempty then vals.min' h else 0)
    rw [dif_neg hv]

lemma mms_rational {m k : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m)) (u : Fin m → ℚ) :
    ∃ r : ℚ,(r:ℝ)=mms G V k (fun v => (u v:ℝ)) := by
  classical
  by_cases hp : (partitions G V k).Nonempty
  · obtain ⟨P,hP,he⟩ := mms_attained G V (fun v => (u v:ℝ)) hp
    rw [he]
    exact partition_value_rational u P
  · refine ⟨0,?_⟩
    have hv : ¬((partitions G V k).image (partitionValue (fun v => (u v:ℝ)))).Nonempty := by
      simpa only [Finset.image_nonempty] using hp
    simp only [mms,Rat.cast_zero,dif_neg hv]

lemma value_mono {m : ℕ} (u : Fin m → ℝ) (hu : ∀ v,0 ≤ u v)
    (S T : Finset (Fin m)) (hST : S ⊆ T) : value u S ≤ value u T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun i hi hni => hu i)

lemma partition_value_le_total {m k : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (u : Fin m → ℝ) (hu : ∀ v,0 ≤ u v) (hk : 0 < k)
    (P : Fin k → Finset (Fin m)) (hP : ConnectedPartition G V P) :
    partitionValue u P ≤ value u V := by
  have hi := (partition_lower_iff u P hk (partitionValue u P)).mp le_rfl (⟨0,hk⟩:Fin k)
  exact hi.trans (value_mono u hu (P ⟨0,hk⟩) V (hP.1 ⟨0,hk⟩).1)

lemma mms_le_total {m k : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (u : Fin m → ℝ) (hu : ∀ v,0 ≤ u v) (hk : 0 < k) : mms G V k u ≤ value u V := by
  classical
  by_cases hp : (partitions G V k).Nonempty
  · obtain ⟨P,hP,he⟩ := mms_attained G V u hp
    rw [he]
    exact partition_value_le_total G V u hu hk P hP
  · have hv : ¬((partitions G V k).image (partitionValue u)).Nonempty := by
      simpa only [Finset.image_nonempty] using hp
    simp only [mms,dif_neg hv]
    exact Finset.sum_nonneg (fun i hi => hu i)

lemma residual_thresholds_prevent_shortfall {m n : ℕ} (G : SimpleGraph (Fin m))
    (u : Fin n → Fin m → ℝ) (q : Fin n → ℚ) (s : Residual m n)
    (hu : ∀ i v,0 ≤ u i v) (hs : 0 < s.agents.card)
    (hq : ∀ i ∈ s.agents,(q i:ℝ) ≤ mms G s.vertices s.agents.card (u i)) :
    ¬Shortfall u q s := by
  rintro ⟨i,hi,hlt⟩
  have hb := (hq i hi).trans (mms_le_total G s.vertices (u i) (hu i) hs)
  exact (not_lt_of_ge hb) hlt
end Queelius.TreeMMS

theorem prior_threshold_bridge : (
  (∀ (m n : Nat) (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → Real) (q : Fin n → Rat),
      @FairDivisionGraph.TreeMMS.IsCFD m n u →
        @SimpleGraph.IsTree (Fin m) G →
          (∀ (i : Fin n),
              @LE.le Real Real.instLE (@Rat.cast Real Real.instRatCast (q i))
                (@FairDivisionGraph.TreeMMS.mms m G (@Finset.univ (Fin m) (Fin.fintype m)) n (u i))) →
            @Exists (Fin n → Finset (Fin m)) fun (π : Fin n → Finset (Fin m)) =>
              And (@FairDivisionGraph.TreeMMS.Valid m n G π)
                (∀ (i : Fin n),
                  @LE.le Real Real.instLE (@Rat.cast Real Real.instRatCast (q i))
                    (@FairDivisionGraph.TreeMMS.value m (u i) (π i)))) →
    ∀ (m n : Nat) (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → Real),
      @FairDivisionGraph.TreeMMS.IsCFD m n u →
        @SimpleGraph.IsTree (Fin m) G →
          @Exists (Fin n → Finset (Fin m)) fun (π : Fin n → Finset (Fin m)) => @FairDivisionGraph.TreeMMS.IsMMS m n G u π
) := @Queelius.TreeMMS.threshold_existence_bridge

namespace Queelius.TreeExecution
open FairDivisionGraph.TreeMMS

lemma descendants_subset {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m)) (r v : Fin m) :
    descendants G V r v ⊆ V := by
  classical
  exact Finset.filter_subset _ _

lemma remove_card {m n : ℕ} (G : SimpleGraph (Fin m)) (s : Residual m n)
    (r v : Fin m) (i : Fin n) (hi : i ∈ s.agents) :
    (remove G s r v i).agents.card + 1 = s.agents.card := by
  exact Finset.card_erase_add_one hi

lemma recurses_card {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s t : Residual m n) (h : Recurses G u q s t) :
    t.agents.card + 1 = s.agents.card := by
  obtain ⟨hs,hc,r,v,i,he,rfl⟩ := h
  exact remove_card G s r v i he.2.2.1

lemma execution_total {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s : Residual m n) : ∃ out,Execution G u q s out := by
  classical
  suffices ∀ k,∀ s : Residual m n,s.agents.card = k → ∃ out,Execution G u q s out from this _ s rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro s hcard
    by_cases hf : FailsHere G u q s
    · exact ⟨none,Execution.fail s hf⟩
    have hs : ¬Shortfall u q s := fun h => hf (Or.inl h)
    by_cases hc : s.agents.card = 1
    · exact ⟨_,Execution.single s hs hc⟩
    have hz : s.agents.card ≠ 0 := fun h => hf (Or.inr (Or.inl h))
    have hgt : 1 < s.agents.card := by omega
    have he : ∃ r v i,Eligible G u q s r v i := by
      by_contra hn
      exact hf (Or.inr (Or.inr ⟨hgt,hn⟩))
    obtain ⟨r,v,i,he⟩ := he
    have hlt : (remove G s r v i).agents.card < k := by
      have hh := remove_card G s r v i he.2.2.1
      omega
    obtain ⟨out,hout⟩ := ih _ hlt (remove G s r v i) rfl
    exact ⟨_,Execution.recurse s r v i out hs hgt he hout⟩

lemma no_infinite_recursion {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (states : ℕ → Residual m n) : ¬∀ k,Recurses G u q (states k) (states (k + 1)) := by
  intro h
  have hc : ∀ k,(states k).agents.card + k = (states 0).agents.card := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := recurses_card G u q _ _ (h k)
      omega
  have hh := hc ((states 0).agents.card + 1)
  omega

structure Certificate {m n : ℕ} (u : Fin n → Fin m → ℝ) (q : Fin n → ℚ)
    (s : Residual m n) (π : Fin n → Finset (Fin m)) : Prop where
  support : ∀ j,π j ⊆ s.vertices
  outside : ∀ j,j ∉ s.agents → π j = ∅
  pairwise : ∀ i j,i ≠ j → Disjoint (π i) (π j)
  threshold : ∀ j ∈ s.agents,(q j : ℝ) ≤ value (u j) (π j)
  covers : ∀ x ∈ s.vertices,∃ j ∈ s.agents,x ∈ π j

lemma execution_certificate {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s : Residual m n) (out : Option (Fin n → Finset (Fin m)))
    (hex : Execution G u q s out) : ∀ π,out = some π → Certificate u q s π := by
  classical
  induction hex with
  | fail s hf => intro π h;cases h
  | single s hs hc =>
    intro π h
    cases h
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hc
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro j;split_ifs <;> simp
    · intro j hj;simp [hj]
    · intro i j hij
      by_cases hi : i ∈ s.agents
      · have hj : j ∉ s.agents := by
          intro hj
          have hi' : i = a := by simpa [ha] using hi
          have hj' : j = a := by simpa [ha] using hj
          exact hij (hi'.trans hj'.symm)
        simp [hj]
      · simp [hi]
    · intro j hj
      simp only [if_pos hj]
      exact le_of_not_gt (fun hh => hs ⟨j,hj,hh⟩)
    · intro x hx
      refine ⟨a,by simp [ha],?_⟩
      simpa [ha] using hx
  | recurse s r v i out hs hc he hex ih =>
    intro π h
    cases out with
    | none => simp at h
    | some previous =>
      simp only [Option.map_some,Option.some.injEq] at h
      subst π
      have cert := ih previous rfl
      have hi : i ∈ s.agents := he.2.2.1
      have hD := descendants_subset G s.vertices r v
      refine ⟨?_,?_,?_,?_,?_⟩
      · intro j
        by_cases hj : j = i
        · subst j;simpa using hD
        · have hh := (cert.support j).trans (Finset.sdiff_subset : s.vertices \ descendants G s.vertices r v ⊆ s.vertices)
          simpa [Function.update,hj,Ne.symm hj] using hh
      · intro j hj
        have hji : j ≠ i := by intro hh;subst j;exact hj hi
        have hje : j ∉ (remove G s r v i).agents := by
          intro hh
          exact hj (Finset.mem_of_mem_erase hh)
        simpa [Function.update,hji,Ne.symm hji] using cert.outside j hje
      · intro a b hab
        by_cases ha : a = i
        · subst a
          have hb : b ≠ i := Ne.symm hab
          have hd : Disjoint (descendants G s.vertices r v) (previous b) :=
            Finset.disjoint_left.mpr (fun x hx hp => (Finset.mem_sdiff.mp (cert.support b hp)).2 hx)
          simpa [Function.update,hb,Ne.symm hb] using hd
        · by_cases hb : b = i
          · subst b
            have hd : Disjoint (descendants G s.vertices r v) (previous a) :=
              Finset.disjoint_left.mpr (fun x hx hp => (Finset.mem_sdiff.mp (cert.support a hp)).2 hx)
            simpa [Function.update,ha,Ne.symm ha] using hd.symm
          · simpa [Function.update,ha,hb,Ne.symm ha,Ne.symm hb] using cert.pairwise a b hab
      · intro j hj
        by_cases hji : j = i
        · subst j;simpa using he.2.2.2.1
        · have hje : j ∈ (remove G s r v i).agents := Finset.mem_erase.mpr ⟨hji,hj⟩
          simpa [Function.update,hji,Ne.symm hji] using cert.threshold j hje
      · intro x hx
        by_cases hxD : x ∈ descendants G s.vertices r v
        · exact ⟨i,hi,by simpa using hxD⟩
        · have hres : x ∈ (remove G s r v i).vertices := Finset.mem_sdiff.mpr ⟨hx,hxD⟩
          obtain ⟨j,hj,hxj⟩ := cert.covers x hres
          have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          exact ⟨j,Finset.mem_of_mem_erase hj,by simpa [Function.update,hji,Ne.symm hji] using hxj⟩

lemma successful_valid_if_connected {m n : ℕ} (G : SimpleGraph (Fin m))
    (u : Fin n → Fin m → ℝ) (q : Fin n → ℚ) (s : Residual m n) (π : Fin n → Finset (Fin m))
    (hex : Execution G u q s (some π)) (hconn : ∀ i,BundleConnected G (π i)) :
    Valid G π ∧ ∀ i ∈ s.agents,(q i : ℝ) ≤ value (u i) (π i) := by
  have hc := execution_certificate G u q s (some π) hex π rfl
  exact ⟨⟨hconn,hc.pairwise⟩,hc.threshold⟩
end Queelius.TreeExecution

namespace Queelius.TreeGeometry
open FairDivisionGraph.TreeMMS SimpleGraph
lemma suffix_descendants {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (r x v : (V : Set (Fin m))) (p : (G.induce (V : Set (Fin m))).Walk r x)
    (hp : p.IsPath) (hv : v ∈ p.support) :
    ∀ y ∈ (p.dropUntil v hv).support,y.val ∈ descendants G V r.val v.val := by
  classical
  intro y hy
  let pre := p.takeUntil v hv
  let post := p.dropUntil v hv
  let q := pre.append (post.takeUntil y hy)
  have he : q.append (post.dropUntil y hy)=p := by
    dsimp only [q,pre,post]
    rw [← Walk.append_assoc,Walk.take_spec,Walk.take_spec]
  have hq : q.IsPath := Walk.IsPath.of_append_left (by rw [he];exact hp)
  apply Finset.mem_filter.mpr
  refine ⟨y.property,r.property,y.property,q,hq,?_⟩
  apply List.mem_map.mpr
  refine ⟨v,?_,rfl⟩
  exact (Walk.mem_support_append_iff _ _).mpr (Or.inl pre.end_mem_support)
lemma descendants_connected {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (r v : Fin m) : BundleConnected G (descendants G V r v) := by
  classical
  let D := descendants G V r v
  by_cases hD : D=∅
  · exact Or.inl hD
  have hne : D.Nonempty := Finset.nonempty_iff_ne_empty.mpr hD
  obtain ⟨x,hx⟩ := hne
  obtain ⟨hxV,hr,hxV',p,hp,hvp⟩ := Finset.mem_filter.mp hx
  obtain ⟨vv,hvv,hevv⟩ := List.mem_map.mp hvp
  have hvD : v ∈ D := by
    have hh := suffix_descendants G V ⟨r,hr⟩ ⟨x,hxV'⟩ vv p hp hvv vv (p.dropUntil vv hvv).start_mem_support
    simpa only [hevv] using hh
  apply Or.inr
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨v,hvD⟩,?_⟩
  rintro ⟨y,hy⟩
  obtain ⟨hyV,hr',hyV',q,hq,hvq⟩ := Finset.mem_filter.mp hy
  obtain ⟨v',hv',hev'⟩ := List.mem_map.mp hvq
  let tail := q.dropUntil v' hv'
  let raw := tail.map (Embedding.induce (V : Set (Fin m))).toHom
  have hraw : ∀ z ∈ raw.support,z ∈ (D : Set (Fin m)) := by
    intro z hz
    change z ∈ (tail.map (Embedding.induce (V : Set (Fin m))).toHom).support at hz
    rw [Walk.support_map] at hz
    change z ∈ tail.support.map Subtype.val at hz
    obtain ⟨zz,hzz,rfl⟩ := List.mem_map.mp hz
    have hh := suffix_descendants G V ⟨r,hr'⟩ ⟨y,hyV'⟩ v' q hq hv' zz hzz
    change zz.val ∈ descendants G V r v
    simpa only [hev'] using hh
  have hw := raw.induce (D : Set (Fin m)) hraw
  have heStart : (⟨v'.val,hraw _ raw.start_mem_support⟩ : (D : Set (Fin m)))=⟨v,hvD⟩ := Subtype.ext hev'
  have heEnd : (⟨y,hraw _ raw.end_mem_support⟩ : (D : Set (Fin m)))=⟨y,hy⟩ := rfl
  exact ⟨hw.copy heStart heEnd⟩

lemma path_avoids_descendants {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (ha : (G.induce (V : Set (Fin m))).IsAcyclic) (r x : (V : Set (Fin m))) (v : Fin m)
    (p : (G.induce (V : Set (Fin m))).Walk r x) (hp : p.IsPath)
    (hx : x.val ∉ descendants G V r.val v) :
    ∀ y ∈ p.support,y.val ∉ descendants G V r.val v := by
  classical
  intro y hy hyd
  obtain ⟨hyV,hr,hyV',q,hq,hvq⟩ := Finset.mem_filter.mp hyd
  change (G.induce (V : Set (Fin m))).Walk r y at q
  have he : q=p.takeUntil y hy := by
    have hh := (ha.subsingleton_path r y).elim ⟨q,hq⟩ ⟨p.takeUntil y hy,hp.takeUntil hy⟩
    exact congrArg Subtype.val hh
  rw [he] at hvq
  obtain ⟨vv,hvv,hval⟩ := List.mem_map.mp hvq
  apply hx
  exact Finset.mem_filter.mpr ⟨x.property,r.property,x.property,p,hp,
    List.mem_map.mpr ⟨vv,p.support_takeUntil_subset_support hy hvv,hval⟩⟩
lemma complement_connected {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (ha : G.IsAcyclic) (hV : BundleConnected G V) (r v : Fin m) (hr : r ∈ V) :
    BundleConnected G (V \ descendants G V r v) := by
  classical
  let C := V \ descendants G V r v
  by_cases hC : C=∅
  · exact Or.inl hC
  have hc : (G.induce (V : Set (Fin m))).Connected := by
    rcases hV with h | h
    · simpa [h] using hr
    · exact h
  obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hC
  have hxV := (Finset.mem_sdiff.mp hx).1
  have hxD := (Finset.mem_sdiff.mp hx).2
  obtain ⟨px,hpx⟩ := hc.exists_isPath ⟨r,hr⟩ ⟨x,hxV⟩
  have hrD := path_avoids_descendants G V (ha.induce (V : Set (Fin m))) ⟨r,hr⟩ ⟨x,hxV⟩ v px hpx hxD ⟨r,hr⟩ px.start_mem_support
  have hrC : r ∈ C := Finset.mem_sdiff.mpr ⟨hr,hrD⟩
  apply Or.inr
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨r,hrC⟩,?_⟩
  rintro ⟨y,hy⟩
  have hyV := (Finset.mem_sdiff.mp hy).1
  have hyD := (Finset.mem_sdiff.mp hy).2
  obtain ⟨q,hq⟩ := hc.exists_isPath ⟨r,hr⟩ ⟨y,hyV⟩
  let raw := q.map (Embedding.induce (V : Set (Fin m))).toHom
  have hraw : ∀ z ∈ raw.support,z ∈ (C : Set (Fin m)) := by
    intro z hz
    change z ∈ (q.map (Embedding.induce (V : Set (Fin m))).toHom).support at hz
    rw [Walk.support_map] at hz
    change z ∈ q.support.map Subtype.val at hz
    obtain ⟨zz,hzz,rfl⟩ := List.mem_map.mp hz
    exact Finset.mem_sdiff.mpr ⟨zz.property,
      path_avoids_descendants G V (ha.induce (V : Set (Fin m))) ⟨r,hr⟩ ⟨y,hyV⟩ v q hq hyD zz hzz⟩
  exact ⟨raw.induce (C : Set (Fin m)) hraw⟩

lemma execution_connected {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (ha : G.IsAcyclic) (s : Residual m n)
    (out : Option (Fin n → Finset (Fin m))) (hex : Execution G u q s out) :
    ∀ π,out=some π → BundleConnected G s.vertices → ∀ i,BundleConnected G (π i) := by
  classical
  induction hex with
  | fail s hf => intro π h;cases h
  | single s hs hc =>
    intro π h hV i
    cases h
    by_cases hi : i ∈ s.agents
    · simpa [hi] using hV
    · simp only [if_neg hi]
      exact Or.inl rfl
  | recurse s r v i out hs hc he hex ih =>
    intro π h hV j
    cases out with
    | none => simp at h
    | some previous =>
      simp only [Option.map_some,Option.some.injEq] at h
      subst π
      have hres : BundleConnected G (remove G s r v i).vertices :=
        complement_connected G s.vertices ha hV r v he.1
      have hprev := ih previous rfl hres
      by_cases hji : j=i
      · subst j
        simpa using descendants_connected G s.vertices r v
      · simpa [Function.update,hji] using hprev j
lemma successful_valid {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (ha : G.IsAcyclic) (s : Residual m n)
    (hV : BundleConnected G s.vertices) (π : Fin n → Finset (Fin m))
    (hex : Execution G u q s (some π)) : Valid G π ∧ ∀ i ∈ s.agents,(q i:ℝ) ≤ value (u i) (π i) := by
  exact Queelius.TreeExecution.successful_valid_if_connected G u q s π hex
    (execution_connected G u q ha s (some π) hex π rfl hV)
lemma univ_connected {m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Connected) :
    BundleConnected G (Finset.univ : Finset (Fin m)) := by
  apply Or.inr
  have hs : ((Finset.univ : Finset (Fin m)) : Set (Fin m))=Set.univ := by ext x;simp
  rw [hs]
  exact (G.induceUnivIso).connected_iff.mpr hG
lemma initial_success {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (hG : G.IsTree) (π : Fin n → Finset (Fin m))
    (hex : Execution G u q (initial m n) (some π)) :
    Valid G π ∧ Complete π ∧ ∀ i,(q i:ℝ) ≤ value (u i) (π i) := by
  have hv := successful_valid G u q hG.isAcyclic (initial m n) (univ_connected G hG.connected) π hex
  have hc := Queelius.TreeExecution.execution_certificate G u q (initial m n) (some π) hex π rfl
  refine ⟨hv.1,?_,?_⟩
  · intro v
    obtain ⟨i,hi,hvi⟩ := hc.covers v (Finset.mem_univ v)
    exact ⟨i,hvi⟩
  · intro i
    exact hv.2 i (Finset.mem_univ i)

lemma reached_connected {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (hG : G.IsTree) (s : Residual m n) (hs : Reached G u q s) :
    BundleConnected G s.vertices := by
  change Relation.ReflTransGen (Recurses G u q) (initial m n) s at hs
  induction hs with
  | refl => exact univ_connected G hG.connected
  | @tail b c hreach hstep ih =>
    obtain ⟨hshort,hcard,r,v,i,he,rfl⟩ := hstep
    exact complement_connected G b.vertices hG.isAcyclic ih r v he.1
lemma initial_success_mms {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (hG : G.IsTree) (π : Fin n → Finset (Fin m))
    (hex : Execution G u q (initial m n) (some π))
    (hq : ∀ i,mms G Finset.univ n (u i) ≤ (q i:ℝ)) : IsMMS G u π ∧ Complete π := by
  have hh := initial_success G u q hG π hex
  exact ⟨⟨hh.1,fun i => (hq i).trans (hh.2.2 i)⟩,hh.2.1⟩
lemma descendants_root {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (hc : (G.induce (V : Set (Fin m))).Connected) (r : Fin m) (hr : r ∈ V) :
    descendants G V r r=V := by
  classical
  ext x
  constructor
  · exact fun h => (Finset.mem_filter.mp h).1
  · intro hx
    obtain ⟨p,hp⟩ := hc.exists_isPath ⟨r,hr⟩ ⟨x,hx⟩
    exact Finset.mem_filter.mpr ⟨hx,hr,hx,p,hp,List.mem_map.mpr ⟨⟨r,hr⟩,p.start_mem_support,rfl⟩⟩

lemma descendants_trans {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (ha : G.IsAcyclic) (r v w x : Fin m) (hw : w ∈ descendants G V r v)
    (hx : x ∈ descendants G V r w) : x ∈ descendants G V r v := by
  classical
  obtain ⟨hwV,hr,hwV',p,hp,hvp⟩ := Finset.mem_filter.mp hw
  obtain ⟨hxV,hr',hxV',q,hq,hwq⟩ := Finset.mem_filter.mp hx
  obtain ⟨ww,hww,heww⟩ := List.mem_map.mp hwq
  subst w
  change (G.induce (V : Set (Fin m))).Walk ⟨r,hr⟩ ww at p
  have he : p=q.takeUntil ww hww := by
    have hh := ((ha.induce (V : Set (Fin m))).subsingleton_path ⟨r,hr⟩ ww).elim
      ⟨p,hp⟩ ⟨q.takeUntil ww hww,hq.takeUntil hww⟩
    exact congrArg Subtype.val hh
  rw [he] at hvp
  obtain ⟨vv,hvv,hevv⟩ := List.mem_map.mp hvp
  exact Finset.mem_filter.mpr ⟨hxV,hr',hxV',q,hq,
    List.mem_map.mpr ⟨vv,q.support_takeUntil_subset_support hww hvv,hevv⟩⟩
end Queelius.TreeGeometry

namespace Queelius.TreeChoice
open FairDivisionGraph.TreeMMS SimpleGraph Queelius.TreeGeometry
lemma child_excludes_parent {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (ha : G.IsAcyclic) (r v w : Fin m) (hc : Child G V r v w) :
    v ∉ descendants G V r w := by
  classical
  intro hv
  obtain ⟨hwV,hr,hwV',p,hp,hvp⟩ := Finset.mem_filter.mp hc.2.1
  obtain ⟨hvV,hr',hvV',q,hq,hwq⟩ := Finset.mem_filter.mp hv
  obtain ⟨vv,hvv,hev⟩ := List.mem_map.mp hvp
  obtain ⟨ww,hww,hew⟩ := List.mem_map.mp hwq
  subst v
  subst w
  change (G.induce (V : Set (Fin m))).Walk ⟨r,hr⟩ ww at p
  change (G.induce (V : Set (Fin m))).Walk ⟨r,hr⟩ vv at q
  have hadj : (G.induce (V : Set (Fin m))).Adj ww vv := hc.1.symm
  have hh := (ha.induce (V : Set (Fin m))).ne_mem_support_of_support_of_adj_of_isPath hp hq hadj hvv
  exact hh hww
lemma child_card_lt {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (ha : G.IsAcyclic) (r v w : Fin m) (hc : Child G V r v w) :
    (descendants G V r w).card < (descendants G V r v).card := by
  classical
  have hnot := child_excludes_parent G V ha r v w hc
  have hsub : descendants G V r w ⊆ descendants G V r v :=
    fun x hx => descendants_trans G V ha r v w x hc.2.1 hx
  obtain ⟨hwV,hr,hwV',p,hp,hvp⟩ := Finset.mem_filter.mp hc.2.1
  obtain ⟨vv,hvv,hev⟩ := List.mem_map.mp hvp
  subst v
  have hvD : vv.val ∈ descendants G V r vv.val :=
    Finset.mem_filter.mpr ⟨vv.property,hr,vv.property,p.takeUntil vv hvv,hp.takeUntil hvv,
      List.mem_map.mpr ⟨vv,(p.takeUntil vv hvv).end_mem_support,rfl⟩⟩
  exact Finset.card_lt_card (Finset.ssubset_def.mpr ⟨hsub,fun hback => hnot (hback hvD)⟩)
lemma eligible_exists {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s : Residual m n) (ha : G.IsAcyclic)
    (hconn : (G.induce (s.vertices : Set (Fin m))).Connected)
    (hagents : s.agents.Nonempty) (hshort : ¬Shortfall u q s) (r : Fin m) (hr : r ∈ s.vertices) :
    ∃ v i,Eligible G u q s r v i := by
  classical
  let C := s.vertices.filter (fun v => ∃ i ∈ s.agents,(q i:ℝ) ≤ value (u i) (descendants G s.vertices r v))
  obtain ⟨a,haA⟩ := hagents
  have hrC : r ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨hr,a,haA,?_⟩
    rw [descendants_root G s.vertices hconn r hr]
    exact le_of_not_gt (fun h => hshort ⟨a,haA,h⟩)
  obtain ⟨v,hv,hmin⟩ := C.exists_min_image (fun v => (descendants G s.vertices r v).card) ⟨r,hrC⟩
  obtain ⟨hvV,i,hi,hqi⟩ := Finset.mem_filter.mp hv
  refine ⟨v,i,hr,hvV,hi,hqi,?_⟩
  intro w hchild j hj
  by_contra hn
  have hjq : (q j:ℝ) ≤ value (u j) (descendants G s.vertices r w) := le_of_not_gt hn
  have hwV : w ∈ s.vertices := Queelius.TreeExecution.descendants_subset G s.vertices r v hchild.2.1
  have hwC : w ∈ C := Finset.mem_filter.mpr ⟨hwV,j,hj,hjq⟩
  have hle := hmin w hwC
  have hlt := child_card_lt G s.vertices ha r v w hchild
  omega
lemma failure_iff_shortfall {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s : Residual m n) (ha : G.IsAcyclic)
    (hconn : (G.induce (s.vertices : Set (Fin m))).Connected) (hagents : s.agents.Nonempty) :
    FailsHere G u q s ↔ Shortfall u q s := by
  classical
  constructor
  · intro hf
    by_contra hn
    rcases hf with hs | hz | ⟨hgt,hno⟩
    · exact hn hs
    · have hh := Finset.card_pos.mpr hagents;omega
    · let r : (s.vertices : Set (Fin m)) := Classical.choice hconn.nonempty
      obtain ⟨v,i,he⟩ := eligible_exists G u q s ha hconn hagents hn r.val r.property
      exact hno ⟨r.val,v,i,he⟩
  · exact Or.inl
lemma invariant_prevents_failure {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s : Residual m n) (ha : G.IsAcyclic)
    (hconn : (G.induce (s.vertices : Set (Fin m))).Connected) (hagents : s.agents.Nonempty)
    (hu : ∀ i v,0 ≤ u i v)
    (hinv : ∀ i ∈ s.agents,(q i:ℝ) ≤ mms G s.vertices s.agents.card (u i)) :
    ¬FailsHere G u q s := by
  have hh := Queelius.TreeMMS.residual_thresholds_prevent_shortfall G u q s hu
    (Finset.card_pos.mpr hagents) hinv
  exact fun hf => hh ((failure_iff_shortfall G u q s ha hconn hagents).mp hf)

lemma path_boundary {U : Type*} (H : SimpleGraph U) (ha : H.IsAcyclic) (r v a b : U)
    (p : H.Walk r a) (hp : p.IsPath) (hvp : v ∈ p.support)
    (q : H.Walk r b) (hq : q.IsPath) (hvq : v ∉ q.support) (hab : H.Adj a b) : a=v := by
  classical
  have hna : a ∉ q.support := by
    intro haq
    have he : q.takeUntil a haq=p := by
      exact congrArg Subtype.val ((ha.subsingleton_path r a).elim ⟨_,hq.takeUntil haq⟩ ⟨p,hp⟩)
    exact hvq (q.support_takeUntil_subset_support haq (he.symm ▸ hvp))
  have he : p=q.concat hab.symm := by
    exact congrArg Subtype.val ((ha.subsingleton_path r a).elim ⟨p,hp⟩ ⟨_,hq.concat hna hab.symm⟩)
  rw [he,Walk.support_concat] at hvp
  have hv : v=a := by simpa using (List.mem_append.mp hvp).resolve_left hvq
  exact hv.symm
lemma descendant_boundary {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (ha : G.IsAcyclic) (hconn : (G.induce (V : Set (Fin m))).Connected)
    (r v a b : Fin m) (haD : a ∈ descendants G V r v) (hbV : b ∈ V)
    (hbD : b ∉ descendants G V r v) (hab : G.Adj a b) : a=v := by
  classical
  obtain ⟨haV,hr,haV',p,hp,hvp⟩ := Finset.mem_filter.mp haD
  obtain ⟨vv,hvv,hev⟩ := List.mem_map.mp hvp
  obtain ⟨q,hq⟩ := hconn.exists_isPath ⟨r,hr⟩ ⟨b,hbV⟩
  have hvq : vv ∉ q.support := by
    intro hh
    exact hbD (Finset.mem_filter.mpr ⟨hbV,hr,hbV,q,hq,List.mem_map.mpr ⟨vv,hh,hev⟩⟩)
  have he := path_boundary (G.induce (V : Set (Fin m))) (ha.induce (V : Set (Fin m)))
    ⟨r,hr⟩ vv ⟨a,haV'⟩ ⟨b,hbV⟩ p hp hvv q hq hvq hab
  exact (congrArg Subtype.val he).trans hev
lemma child_boundary_parent {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (ha : G.IsAcyclic) (hconn : (G.induce (V : Set (Fin m))).Connected)
    (r v w a b : Fin m) (hchild : Child G V r v w)
    (haD : a ∈ descendants G V r w) (hbV : b ∈ V)
    (hbD : b ∉ descendants G V r w) (hab : G.Adj a b) : b=v := by
  classical
  have hea := descendant_boundary G V ha hconn r w a b haD hbV hbD hab
  subst a
  obtain ⟨hwV,hr,hwV',p,hp,hvp⟩ := Finset.mem_filter.mp hchild.2.1
  obtain ⟨vv,hvv,hev⟩ := List.mem_map.mp hvp
  obtain ⟨q,hq⟩ := hconn.exists_isPath ⟨r,hr⟩ ⟨b,hbV⟩
  have hwq : (⟨w,hwV'⟩ : (V : Set (Fin m))) ∉ q.support := by
    intro hh
    exact hbD (Finset.mem_filter.mpr ⟨hbV,hr,hbV,q,hq,List.mem_map.mpr ⟨⟨w,hwV'⟩,hh,rfl⟩⟩)
  have hadj : (G.induce (V : Set (Fin m))).Adj ⟨b,hbV⟩ ⟨w,hwV'⟩ := hab.symm
  have he : p=q.concat hadj := by
    exact congrArg Subtype.val (((ha.induce (V : Set (Fin m))).subsingleton_path ⟨r,hr⟩ ⟨w,hwV'⟩).elim
      ⟨p,hp⟩ ⟨_,hq.concat hwq hadj⟩)
  have hvadj : (G.induce (V : Set (Fin m))).Adj ⟨w,hwV'⟩ vv := by
    change G.Adj w vv.val
    simpa only [hev] using hchild.1.symm
  have hvpen := (ha.induce (V : Set (Fin m))).eq_penultimate_of_adj_end hp hvadj hvv
  have hbpen : (⟨b,hbV⟩ : (V : Set (Fin m)))=p.penultimate := by rw [he,Walk.penultimate_concat]
  exact (congrArg Subtype.val (hbpen.trans hvpen.symm)).trans hev
lemma walk_in_child {m : ℕ} (G : SimpleGraph (Fin m)) (V P : Finset (Fin m))
    (ha : G.IsAcyclic) (hconn : (G.induce (V : Set (Fin m))).Connected)
    (r v w : Fin m) (hchild : Child G V r v w) (hPV : P ⊆ V) (hvP : v ∉ P)
    (x y : (P : Set (Fin m))) (p : (G.induce (P : Set (Fin m))).Walk x y) :
    x.val ∈ descendants G V r w → y.val ∈ descendants G V r w := by
  induction p with
  | nil => exact id
  | @cons a b c hab p ih =>
    intro haD
    apply ih
    by_contra hbD
    have he := child_boundary_parent G V ha hconn r v w a.val b.val hchild haD (hPV b.property) hbD hab
    exact hvP (he ▸ b.property)
lemma connected_part_in_child {m : ℕ} (G : SimpleGraph (Fin m)) (V P : Finset (Fin m))
    (ha : G.IsAcyclic) (hconn : (G.induce (V : Set (Fin m))).Connected)
    (r v w : Fin m) (hchild : Child G V r v w) (hPV : P ⊆ V) (hvP : v ∉ P)
    (hP : (G.induce (P : Set (Fin m))).Connected) (x : Fin m) (hxP : x ∈ P)
    (hxD : x ∈ descendants G V r w) : P ⊆ descendants G V r w := by
  intro y hy
  obtain ⟨p,hp⟩ := hP.exists_isPath ⟨x,hxP⟩ ⟨y,hy⟩
  exact walk_in_child G V P ha hconn r v w hchild hPV hvP ⟨x,hxP⟩ ⟨y,hy⟩ p hxD

lemma child_containing_vertex {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (r v x : Fin m) (hx : x ∈ descendants G V r v) (hxv : x≠v) :
    ∃ w,Child G V r v w ∧ x ∈ descendants G V r w := by
  classical
  obtain ⟨hxV,hr,hxV',p,hp,hvp⟩ := Finset.mem_filter.mp hx
  obtain ⟨vv,hvv,hev⟩ := List.mem_map.mp hvp
  let tail := p.dropUntil vv hvv
  have hne : vv ≠ (⟨x,hxV'⟩ : (V : Set (Fin m))) := by
    intro he
    exact hxv ((congrArg Subtype.val he).symm.trans hev)
  have htail : ¬tail.Nil := Walk.not_nil_of_ne hne
  have hws : tail.snd ∈ tail.support := List.mem_of_mem_tail (tail.snd_mem_tail_support htail)
  have hwp : tail.snd ∈ p.support := p.support_dropUntil_subset_support hvv hws
  have hwD : tail.snd.val ∈ descendants G V r v := by
    have hh := Queelius.TreeGeometry.suffix_descendants G V ⟨r,hr⟩ ⟨x,hxV'⟩ vv p hp hvv tail.snd hws
    simpa only [hev] using hh
  have hadj : G.Adj v tail.snd.val := by
    have hh := tail.adj_snd htail
    change G.Adj vv.val tail.snd.val at hh
    simpa only [hev] using hh
  refine ⟨tail.snd.val,⟨hadj,hwD,hadj.ne'⟩,?_⟩
  exact Finset.mem_filter.mpr ⟨hxV,hr,hxV',p,hp,List.mem_map.mpr ⟨tail.snd,hwp,rfl⟩⟩
lemma part_in_one_child {m : ℕ} (G : SimpleGraph (Fin m)) (V P : Finset (Fin m))
    (ha : G.IsAcyclic) (hconn : (G.induce (V : Set (Fin m))).Connected)
    (r v : Fin m) (hPV : P ⊆ V) (hvP : v ∉ P)
    (hP : (G.induce (P : Set (Fin m))).Connected) (x : Fin m) (hxP : x ∈ P)
    (hxD : x ∈ descendants G V r v) :
    ∃ w,Child G V r v w ∧ P ⊆ descendants G V r w := by
  have hxv : x≠v := by intro he;exact hvP (he ▸ hxP)
  obtain ⟨w,hw,hxw⟩ := child_containing_vertex G V r v x hxD hxv
  exact ⟨w,hw,connected_part_in_child G V P ha hconn r v w hw hPV hvP hP x hxP hxw⟩
lemma descendants_in_partition_part {m k : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (ha : G.IsAcyclic) (hconn : (G.induce (V : Set (Fin m))).Connected)
    (r v : Fin m) (u : Fin m → ℝ) (hu : ∀ x,0 ≤ u x) (q : ℝ)
    (P : Fin k → Finset (Fin m)) (hP : ConnectedPartition G V P)
    (hvalue : ∀ a,q ≤ value u (P a))
    (hsmall : ∀ w,Child G V r v w → value u (descendants G V r w) < q)
    (a : Fin k) (hva : v ∈ P a) : descendants G V r v ⊆ P a := by
  intro x hx
  have hxV := Queelius.TreeExecution.descendants_subset G V r v hx
  obtain ⟨b,hxb⟩ := (hP.2.2 x).mp hxV
  by_cases he : b=a
  · subst b;exact hxb
  · have hvb : v ∉ P b := by
      intro hvb
      exact (Finset.disjoint_left.mp (hP.2.1 a b (Ne.symm he))) hva hvb
    obtain ⟨w,hw,hsub⟩ := part_in_one_child G V (P b) ha hconn r v
      (hP.1 b).1 hvb (hP.1 b).2.2 x hxb hx
    have hvle := Queelius.TreeMMS.value_mono u hu (P b) (descendants G V r w) hsub
    exact False.elim ((not_lt_of_ge ((hvalue b).trans hvle)) (hsmall w hw))

lemma partition_value_nonneg {m k : ℕ} (u : Fin m → ℝ) (hu : ∀ x,0 ≤ u x)
    (P : Fin k → Finset (Fin m)) : 0 ≤ partitionValue u P := by
  classical
  let vals := Finset.univ.image (fun j => value u (P j))
  by_cases hv : vals.Nonempty
  · change 0 ≤ if h : vals.Nonempty then vals.min' h else 0
    rw [dif_pos hv,Finset.le_min'_iff]
    intro x hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.sum_nonneg (fun x hx => hu x)
  · change 0 ≤ if h : vals.Nonempty then vals.min' h else 0
    simp only [dif_neg hv,le_refl]
lemma mms_nonneg {m k : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (u : Fin m → ℝ) (hu : ∀ x,0 ≤ u x) : 0 ≤ mms G V k u := by
  classical
  by_cases hp : (partitions G V k).Nonempty
  · obtain ⟨P,hP,he⟩ := Queelius.TreeMMS.mms_attained G V u hp
    rw [he]
    exact partition_value_nonneg u hu P
  · have hv : ¬((partitions G V k).image (partitionValue u)).Nonempty := by
      simpa only [Finset.image_nonempty] using hp
    simp only [mms,dif_neg hv,le_refl]
lemma positive_threshold_partition {m k : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (u : Fin m → ℝ) (q : ℝ) (hk : 0 < k) (hqpos : 0 < q) (hq : q ≤ mms G V k u) :
    ∃ P : Fin k → Finset (Fin m),ConnectedPartition G V P ∧ ∀ a,q ≤ value u (P a) := by
  classical
  by_cases hp : (partitions G V k).Nonempty
  · exact (Queelius.TreeMMS.mms_threshold_iff G V u hk hp q).mp hq
  · have hv : ¬((partitions G V k).image (partitionValue u)).Nonempty := by
      simpa only [Finset.image_nonempty] using hp
    have hz : mms G V k u=0 := by simp only [mms,dif_neg hv]
    rw [hz] at hq
    linarith
lemma eligible_partition_alignment {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s : Residual m n) (ha : G.IsAcyclic)
    (hconn : (G.induce (s.vertices : Set (Fin m))).Connected)
    (r v : Fin m) (i j : Fin n) (he : Eligible G u q s r v i) (hj : j ∈ s.agents)
    (hu : ∀ x,0 ≤ u j x) (hqpos : (0:ℝ) < (q j:ℝ))
    (hq : (q j:ℝ) ≤ mms G s.vertices s.agents.card (u j)) :
    ∃ P : Fin s.agents.card → Finset (Fin m),ConnectedPartition G s.vertices P ∧
      (∀ a,(q j:ℝ) ≤ value (u j) (P a)) ∧
      ∃ a,v ∈ P a ∧ descendants G s.vertices r v ⊆ P a := by
  obtain ⟨P,hP,hval⟩ := positive_threshold_partition G s.vertices (u j) (q j:ℝ)
    (Finset.card_pos.mpr ⟨i,he.2.2.1⟩) hqpos hq
  obtain ⟨a,hva⟩ := (hP.2.2 v).mp he.2.1
  refine ⟨P,hP,hval,a,hva,?_⟩
  exact descendants_in_partition_part G s.vertices ha hconn r v (u j) hu (q j:ℝ) P hP hval
    (fun w hw => he.2.2.2.2 w hw j hj) a hva
end Queelius.TreeChoice

namespace Queelius.TreePartition
open SimpleGraph FairDivisionGraph.TreeMMS
noncomputable section
lemma path_inside {U : Type*} (G : SimpleGraph U) (ha : G.IsAcyclic) (A : Set U)
    (hA : (G.induce A).Connected) (x y : U) (hx : x ∈ A) (hy : y ∈ A)
    (p : G.Walk x y) (hp : p.IsPath) : ∀ z ∈ p.support,z ∈ A := by
  obtain ⟨q,hq⟩ := hA.exists_isPath ⟨x,hx⟩ ⟨y,hy⟩
  let raw := q.map (Embedding.induce A).toHom
  have hraw : raw.IsPath := hq.map (Embedding.induce (G:=G) A).injective
  have he : raw=p := by
    have hh := (ha.subsingleton_path x y).elim ⟨raw,hraw⟩ ⟨p,hp⟩
    exact congrArg Subtype.val hh
  intro z hz
  rw [← he] at hz
  change z ∈ (q.map (Embedding.induce A).toHom).support at hz
  rw [Walk.support_map] at hz
  change z ∈ q.support.map Subtype.val at hz
  obtain ⟨zz,hzz,rfl⟩ := List.mem_map.mp hz
  exact zz.property
lemma intersection_connected {U : Type*} (G : SimpleGraph U) (ha : G.IsAcyclic) (A B : Set U)
    (hA : (G.induce A).Connected) (hB : (G.induce B).Connected) (hne : (A ∩ B).Nonempty) :
    (G.induce (A ∩ B)).Connected := by
  obtain ⟨x,hx⟩ := hne
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨x,hx⟩,?_⟩
  rintro ⟨y,hy⟩
  obtain ⟨p,hp⟩ := hA.exists_isPath ⟨x,hx.1⟩ ⟨y,hy.1⟩
  let raw := p.map (Embedding.induce A).toHom
  have hr : raw.IsPath := hp.map (Embedding.induce (G:=G) A).injective
  have hs : ∀ z ∈ raw.support,z ∈ A ∩ B := by
    intro z hz
    exact ⟨path_inside G ha A hA x y hx.1 hy.1 raw hr z hz,
      path_inside G ha B hB x y hx.2 hy.2 raw hr z hz⟩
  exact ⟨raw.induce (A ∩ B) hs⟩
lemma crossing {U : Type*} (G : SimpleGraph U) (A : U → Prop) {x y : U}
    (p : G.Walk x y) (hx : A x) (hy : ¬A y) : ∃ a b,G.Adj a b ∧ A a ∧ ¬A b := by
  classical
  induction p with
  | nil => exact (hy hx).elim
  | @cons x z y h p ih =>
    by_cases hz : A z
    · exact ih hz hy
    · exact ⟨x,z,h,hx,hz⟩
lemma residual_other_part {m k : ℕ} (G : SimpleGraph (Fin m)) (V D : Finset (Fin m))
    (P : Fin (k+1) → Finset (Fin m)) (hP : ConnectedPartition G V P)
    (a b : Fin (k+1)) (hD : D ⊆ P a) (hb : b≠a) : P b ⊆ V \ D := by
  intro x hx
  refine Finset.mem_sdiff.mpr ⟨(hP.1 b).1 hx,?_⟩
  intro hxD
  exact Finset.disjoint_left.mp (hP.2.1 b a hb) hx (hD hxD)
lemma remainder_connected {m k : ℕ} (G : SimpleGraph (Fin m)) (ha : G.IsAcyclic)
    (V D : Finset (Fin m)) (P : Fin (k+1) → Finset (Fin m)) (hP : ConnectedPartition G V P)
    (a : Fin (k+1)) (hC : (G.induce ((V \ D : Finset (Fin m)) : Set (Fin m))).Connected)
    (hR : (P a \ D).Nonempty) : (G.induce ((P a \ D : Finset (Fin m)) : Set (Fin m))).Connected := by
  have he : ((P a : Set (Fin m)) ∩ ((V \ D : Finset (Fin m)) : Set (Fin m)))=
      ((P a \ D : Finset (Fin m)) : Set (Fin m)) := by
    ext x
    simp only [Set.mem_inter_iff,Finset.mem_coe,Finset.mem_sdiff]
    constructor
    · intro h;exact ⟨h.1,h.2.2⟩
    · intro h;exact ⟨h.1,(hP.1 a).1 h.1,h.2⟩
  rw [← he]
  apply intersection_connected G ha _ _ (hP.1 a).2.2 hC
  rw [he]
  exact hR
end
end Queelius.TreePartition

namespace Queelius.TreePartition
open SimpleGraph FairDivisionGraph.TreeMMS
noncomputable section
lemma merge_choice {m k : ℕ} (hk : 0 < k) (G : SimpleGraph (Fin m)) (ha : G.IsAcyclic)
    (V D : Finset (Fin m)) (P : Fin (k+1) → Finset (Fin m)) (hP : ConnectedPartition G V P)
    (a : Fin (k+1)) (hD : D ⊆ P a)
    (hC : (G.induce ((V \ D : Finset (Fin m)) : Set (Fin m))).Connected) :
    ∃ c : Fin (k+1),c≠a ∧
      (G.induce (((P a \ D) ∪ P c : Finset (Fin m)) : Set (Fin m))).Connected := by
  let c0 := a.succAbove ⟨0,hk⟩
  have hc0 : c0≠a := Fin.succAbove_ne a ⟨0,hk⟩
  by_cases hR : P a \ D=∅
  · refine ⟨c0,hc0,?_⟩
    rw [hR,Finset.empty_union]
    exact (hP.1 c0).2.2
  have hRc := remainder_connected G ha V D P hP a hC (Finset.nonempty_iff_ne_empty.mpr hR)
  obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hR
  obtain ⟨y,hy⟩ := (hP.1 c0).2.1
  have hxC : x ∈ V \ D := Finset.mem_sdiff.mpr ⟨(hP.1 a).1 (Finset.mem_sdiff.mp hx).1,(Finset.mem_sdiff.mp hx).2⟩
  have hyC := residual_other_part G V D P hP a c0 hD hc0 hy
  have hyR : y ∉ P a \ D := by
    intro h
    exact Finset.disjoint_left.mp (hP.2.1 c0 a hc0) hy (Finset.mem_sdiff.mp h).1
  obtain ⟨p,hp⟩ := hC.exists_isPath ⟨x,hxC⟩ ⟨y,hyC⟩
  obtain ⟨aa,bb,hab,haa,hbb⟩ := crossing (G.induce ((V \ D : Finset (Fin m)) : Set (Fin m)))
    (fun z => z.val ∈ P a \ D) p hx hyR
  obtain ⟨c,hbc⟩ := (hP.2.2 bb.val).mp (Finset.mem_sdiff.mp bb.property).1
  have hca : c≠a := by
    intro he
    apply hbb
    exact Finset.mem_sdiff.mpr ⟨he ▸ hbc,(Finset.mem_sdiff.mp bb.property).2⟩
  refine ⟨c,hca,?_⟩
  have hh := connected_induce_union hRc.preconnected (hP.1 c).2.2.preconnected haa hbc hab
  rw [Finset.coe_union]
  exact hh
lemma delete_subset_partition {m k : ℕ} (hk : 0 < k) (G : SimpleGraph (Fin m)) (ha : G.IsAcyclic)
    (V D : Finset (Fin m)) (P : Fin (k+1) → Finset (Fin m)) (hP : ConnectedPartition G V P)
    (a : Fin (k+1)) (hD : D ⊆ P a)
    (hC : (G.induce ((V \ D : Finset (Fin m)) : Set (Fin m))).Connected)
    (u : Fin m → ℝ) (hu : ∀ x,0 ≤ u x) (q : ℝ) (hq : ∀ b,q ≤ value u (P b)) :
    ∃ Q : Fin k → Finset (Fin m),ConnectedPartition G (V \ D) Q ∧ ∀ b,q ≤ value u (Q b) := by
  obtain ⟨c,hca,hconn⟩ := merge_choice hk G ha V D P hP a hD hC
  let R := P a \ D
  let W : Fin (k+1) → Finset (Fin m) := fun b => if b=c then R ∪ P b else P b
  have hRsub : R ⊆ V \ D := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨(hP.1 a).1 (Finset.mem_sdiff.mp hx).1,(Finset.mem_sdiff.mp hx).2⟩
  have hWP : ∀ b,P b ⊆ W b := by
    intro b
    dsimp only [W]
    split_ifs
    · exact Finset.subset_union_right
    · exact Finset.Subset.refl _
  have hWsub : ∀ b,b≠a → W b ⊆ V \ D := by
    intro b hba
    dsimp only [W]
    split_ifs
    · exact Finset.union_subset hRsub (residual_other_part G V D P hP a b hD hba)
    · exact residual_other_part G V D P hP a b hD hba
  have hWconn : ∀ b,b≠a → (G.induce (W b : Set (Fin m))).Connected := by
    intro b hba
    by_cases he : b=c
    · subst b
      have heq : W c=(P a \ D) ∪ P c := by simp only [W,R,if_pos rfl]
      rw [heq]
      exact hconn
    · have heq : W b=P b := by simp only [W,if_neg he]
      rw [heq]
      exact (hP.1 b).2.2
  have hRdis : ∀ b,b≠a → Disjoint R (P b) := by
    intro b hba
    exact (hP.2.1 a b (Ne.symm hba)).mono_left Finset.sdiff_subset
  have hWdis : ∀ b l,b≠a → l≠a → b≠l → Disjoint (W b) (W l) := by
    intro b l hba hla hbl
    by_cases hb : b=c
    · by_cases hl : l=c
      · exact (hbl (hb.trans hl.symm)).elim
      · simp only [W,if_pos hb,if_neg hl]
        exact Finset.disjoint_union_left.mpr ⟨hRdis l hla,hP.2.1 b l hbl⟩
    · by_cases hl : l=c
      · simp only [W,if_neg hb,if_pos hl]
        exact Finset.disjoint_union_right.mpr ⟨(hRdis b hba).symm,hP.2.1 b l hbl⟩
      · simpa only [W,if_neg hb,if_neg hl] using hP.2.1 b l hbl
  have hWcover : ∀ x,x ∈ V \ D ↔ ∃ b,b≠a ∧ x ∈ W b := by
    intro x
    constructor
    · intro hx
      obtain ⟨b,hxb⟩ := (hP.2.2 x).mp (Finset.mem_sdiff.mp hx).1
      by_cases he : b=a
      · refine ⟨c,hca,?_⟩
        have hxR : x ∈ R := Finset.mem_sdiff.mpr ⟨he ▸ hxb,(Finset.mem_sdiff.mp hx).2⟩
        exact (show R ⊆ W c by simp only [W,if_pos rfl];exact Finset.subset_union_left) hxR
      · exact ⟨b,he,hWP b hxb⟩
    · rintro ⟨b,hba,hxb⟩;exact hWsub b hba hxb
  let Q : Fin k → Finset (Fin m) := fun j => W (a.succAbove j)
  refine ⟨Q,⟨?_,?_,?_⟩,?_⟩
  · intro j
    exact ⟨hWsub _ (Fin.succAbove_ne a j),(hP.1 (a.succAbove j)).2.1.mono (hWP _),hWconn _ (Fin.succAbove_ne a j)⟩
  · intro j l hjl
    exact hWdis _ _ (Fin.succAbove_ne a j) (Fin.succAbove_ne a l)
      (fun he => hjl (Fin.succAbove_right_injective he))
  · intro x
    constructor
    · intro hx
      obtain ⟨b,hba,hxb⟩ := (hWcover x).mp hx
      obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hba
      exact ⟨j,by simpa only [Q,hj] using hxb⟩
    · rintro ⟨j,hj⟩;exact hWsub _ (Fin.succAbove_ne a j) hj
  · intro j
    exact (hq (a.succAbove j)).trans (Queelius.TreeMMS.value_mono u hu _ _ (hWP _))
end
end Queelius.TreePartition

namespace Queelius.TreePartition
open SimpleGraph FairDivisionGraph.TreeMMS
noncomputable section
lemma mms_delete_subset {m K : ℕ} (hK : 1 < K) (G : SimpleGraph (Fin m)) (ha : G.IsAcyclic)
    (V D : Finset (Fin m)) (P : Fin K → Finset (Fin m)) (hP : ConnectedPartition G V P)
    (a : Fin K) (hD : D ⊆ P a) (hC : BundleConnected G (V \ D))
    (u : Fin m → ℝ) (hu : ∀ x,0 ≤ u x) (q : ℝ) (hq : ∀ b,q ≤ value u (P b)) :
    q ≤ mms G (V \ D) (K-1) u := by
  cases K with
  | zero => omega
  | succ k =>
    have hk : 0 < k := by omega
    let b := a.succAbove ⟨0,hk⟩
    have hba : b≠a := Fin.succAbove_ne a ⟨0,hk⟩
    obtain ⟨x,hx⟩ := (hP.1 b).2.1
    have hxC := residual_other_part G V D P hP a b hD hba hx
    have hconn : (G.induce ((V \ D : Finset (Fin m)) : Set (Fin m))).Connected := by
      rcases hC with hzero | hc
      · rw [hzero] at hxC;simp at hxC
      · exact hc
    obtain ⟨Q,hQ,hvals⟩ := delete_subset_partition hk G ha V D P hP a hD hconn u hu q hq
    change q ≤ mms G (V \ D) k u
    exact ((Queelius.TreeMMS.partition_lower_iff u Q hk q).mpr hvals).trans
      (Queelius.TreeMMS.partition_le_mms G (V \ D) u Q hQ)
lemma eligible_mms {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s : Residual m n) (ha : G.IsAcyclic)
    (hconn : (G.induce (s.vertices : Set (Fin m))).Connected)
    (hK : 1 < s.agents.card) (r v : Fin m) (i j : Fin n)
    (he : Eligible G u q s r v i) (hj : j ∈ s.agents)
    (hu : ∀ x,0 ≤ u j x) (hqpos : (0:ℝ) < (q j:ℝ))
    (hq : (q j:ℝ) ≤ mms G s.vertices s.agents.card (u j)) :
    (q j:ℝ) ≤ mms G (remove G s r v i).vertices (remove G s r v i).agents.card (u j) := by
  obtain ⟨P,hP,hval,a,hva,hD⟩ := Queelius.TreeChoice.eligible_partition_alignment
    G u q s ha hconn r v i j he hj hu hqpos hq
  have hC := Queelius.TreeGeometry.complement_connected G s.vertices ha (Or.inr hconn) r v he.1
  have hh := mms_delete_subset hK G ha s.vertices (descendants G s.vertices r v) P hP a hD hC
    (u j) hu (q j:ℝ) hval
  have hc := Queelius.TreeExecution.remove_card G s r v i he.2.2.1
  have hcard : (remove G s r v i).agents.card=s.agents.card-1 := by omega
  rw [hcard]
  exact hh
lemma residual_invariant {m n : ℕ} (G : SimpleGraph (Fin m))
    (u : Fin n → Fin m → ℝ) (q : Fin n → ℚ)
    (hCFD : IsCFD u) (hTree : G.IsTree)
    (hq : ∀ i,(q i:ℝ) ≤ mms G Finset.univ n (u i))
    (s : Residual m n) (hs : Reached G u q s) :
    ∀ j ∈ s.agents,(q j:ℝ) ≤ mms G s.vertices s.agents.card (u j) := by
  change Relation.ReflTransGen (Recurses G u q) (initial m n) s at hs
  induction hs with
  | refl =>
    intro j hj
    simpa only [initial,Finset.card_univ,Fintype.card_fin] using hq j
  | @tail b c hreach hstep ih =>
    obtain ⟨hshort,hK,r,v,i,he,rfl⟩ := hstep
    intro j hj
    have hjold : j ∈ b.agents := Finset.mem_of_mem_erase hj
    have hu : ∀ x,0 ≤ u j x := hCFD.2.2.1 j
    by_cases hqpos : (0:ℝ) < (q j:ℝ)
    · obtain ⟨P,hP,hval⟩ := Queelius.TreeChoice.positive_threshold_partition G b.vertices (u j) (q j:ℝ)
        (by omega) hqpos (ih j hjold)
      let a : Fin b.agents.card := ⟨0,by omega⟩
      obtain ⟨x,hx⟩ := (hP.1 a).2.1
      have hxV := (hP.1 a).1 hx
      have hconn : (G.induce (b.vertices : Set (Fin m))).Connected := by
        rcases Queelius.TreeGeometry.reached_connected G u q hTree b hreach with hzero | hc
        · rw [hzero] at hxV;simp at hxV
        · exact hc
      exact eligible_mms G u q b hTree.isAcyclic hconn hK r v i j he hjold hu hqpos (ih j hjold)
    · exact (le_of_not_gt hqpos).trans (Queelius.TreeChoice.mms_nonneg G _ (u j) hu)
end
end Queelius.TreePartition

theorem solution : (
  ∀ {m n : Nat} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → Real) (q : Fin n → Rat),
    @FairDivisionGraph.TreeMMS.IsCFD m n u →
      @SimpleGraph.IsTree (Fin m) G →
        (∀ (i : Fin n),
            @LE.le Real Real.instLE (@Rat.cast Real Real.instRatCast (q i))
              (@FairDivisionGraph.TreeMMS.mms m G (@Finset.univ (Fin m) (Fin.fintype m)) n (u i))) →
          ∀ (s : FairDivisionGraph.TreeMMS.Residual m n),
            @FairDivisionGraph.TreeMMS.Reached m n G u q s →
              ∀ (j : Fin n),
                @Membership.mem (Fin n) (Finset (Fin n))
                    (@SetLike.instMembership (Finset (Fin n)) (Fin n) (@Finset.instSetLike (Fin n)))
                    (@FairDivisionGraph.TreeMMS.Residual.agents m n s) j →
                  @LE.le Real Real.instLE (@Rat.cast Real Real.instRatCast (q j))
                    (@FairDivisionGraph.TreeMMS.mms m G (@FairDivisionGraph.TreeMMS.Residual.vertices m n s)
                      (@Finset.card (Fin n) (@FairDivisionGraph.TreeMMS.Residual.agents m n s)) (u j))
) := @Queelius.TreePartition.residual_invariant
