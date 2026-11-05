-- Prove2me | solution 1 for CoffmanMitrani.theorem_1_mixing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T13:46:07.717163+00:00
-- url     : https://prove2.me/submissions/605e4995-15fa-4d23-b3ae-4b193c17c9f9

import Mathlib
import Definitions.Def_CoffmanMitrani_IsStrategy
import Definitions.Def_CoffmanMitrani_Achieves
import Definitions.Def_CoffmanMitrani_mix
import Definitions.Def_CoffmanMitrani_Data_P
import Definitions.Def_CoffmanMitrani_arrival

/-! # 27b64375 CoffmanMitrani.theorem_1_mixing: the mixing strategy is a strategy and achieves the mixture.
Layers: CMX (deterministic busy-period locality), CMY (seed independence), CMA (no arrival ties a.s.),
CMQ (opener events measurable mod null), CMP (finitely many arrivals in bounded windows a.s.),
CMZ (bridge to the platform definitions, IsStrategy, Achieves), CMW (Fubini over the seed array). -/


/-! # 27b64375 deterministic layer (Mathlib only): busy-period locality of work-conserving schedules.

Generic data: arrival epochs `a`, service requirements `r`, schedule `S : ℝ → Option ι`.
`srv`, `pres`, `wIn`, `BPS`, `InB` are the platform `served`, `present`, `workIn`, `IsBPStart`, `InBP`
with `a := arrival ω`, `r := serviceReq ω`, `S := S ω` (defeq). -/

set_option autoImplicit false

namespace CMX
open MeasureTheory Set

variable {ι : Type*}

noncomputable def srv (S : ℝ → Option ι) (j : ι) (t : ℝ) : ℝ :=
  (volume ({s : ℝ | S s = some j} ∩ Ico 0 t)).toReal

def pres (a r : ι → ℝ) (S : ℝ → Option ι) (j : ι) (t : ℝ) : Prop :=
  a j ≤ t ∧ srv S j t < r j

noncomputable def wIn (a r : ι → ℝ) (s t : ℝ) : ℝ :=
  ∑' j : ι, Set.indicator {j : ι | s ≤ a j ∧ a j < t} r j

def BPS (a r : ι → ℝ) (j0 : ι) : Prop := ∀ s ≤ a j0, wIn a r s (a j0) ≤ a j0 - s

def InB (a r : ι → ℝ) (j0 : ι) (t : ℝ) : Prop :=
  a j0 ≤ t ∧ ∀ s ∈ Ioc (a j0) t, s - a j0 < wIn a r (a j0) s

def IdlePt (a r : ι → ℝ) (t : ℝ) : Prop := ∀ s ≤ t, wIn a r s t ≤ t - s

structure DGood (a r : ι → ℝ) : Prop where
  apos : ∀ j, 0 < a j
  rpos : ∀ j, 0 < r j
  fin : ∀ T : ℝ, {j | a j ≤ T}.Finite

structure SGood (a r : ι → ℝ) (S : ℝ → Option ι) : Prop where
  feas : ∀ t j, S t = some j → pres a r S j t
  idle : ∀ t, S t = none ↔ ∀ j, ¬ pres a r S j t
  meas : ∀ j, NullMeasurableSet {s : ℝ | S s = some j}

/-! ## served -/

section srv
variable (S : ℝ → Option ι) (j : ι)

lemma vol_Ico_ne_top (s t : ℝ) (A : Set ℝ) : volume (A ∩ Ico s t) ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (measure_mono inter_subset_right)

lemma srv_nonneg (t : ℝ) : 0 ≤ srv S j t := ENNReal.toReal_nonneg

lemma srv_split {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    srv S j t = srv S j s + (volume ({u : ℝ | S u = some j} ∩ Ico s t)).toReal := by
  unfold srv
  have h := measure_inter_add_sdiff ({u : ℝ | S u = some j} ∩ Ico 0 t) (μ := volume)
    (measurableSet_Ico (a := (0:ℝ)) (b := s))
  have e1 : {u : ℝ | S u = some j} ∩ Ico 0 t ∩ Ico 0 s = {u : ℝ | S u = some j} ∩ Ico 0 s := by
    ext u; simp only [mem_inter_iff, mem_Ico]; constructor
    · rintro ⟨⟨h1, _, _⟩, h3, h4⟩; exact ⟨h1, h3, h4⟩
    · rintro ⟨h1, h3, h4⟩; exact ⟨⟨h1, h3, by linarith⟩, h3, h4⟩
  have e2 : ({u : ℝ | S u = some j} ∩ Ico 0 t) \ Ico 0 s = {u : ℝ | S u = some j} ∩ Ico s t := by
    ext u; simp only [mem_inter_iff, mem_diff, mem_Ico, not_and, not_lt]; constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h4 h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by linarith, h3⟩, fun _ => h2⟩
  rw [e1, e2] at h
  rw [← h, ENNReal.toReal_add (vol_Ico_ne_top _ _ _) (vol_Ico_ne_top _ _ _)]

lemma srv_mono {s t : ℝ} (hst : s ≤ t) : srv S j s ≤ srv S j t := by
  unfold srv
  refine ENNReal.toReal_mono (vol_Ico_ne_top _ _ _) (measure_mono ?_)
  intro u ⟨h1, h2, h3⟩; exact ⟨h1, h2, by linarith⟩

lemma piece_le {s t : ℝ} (hst : s ≤ t) :
    (volume ({u : ℝ | S u = some j} ∩ Ico s t)).toReal ≤ t - s := by
  have : volume ({u : ℝ | S u = some j} ∩ Ico s t) ≤ ENNReal.ofReal (t - s) := by
    rw [← Real.volume_Ico]; exact measure_mono inter_subset_right
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
  rwa [ENNReal.toReal_ofReal (by linarith)] at this

lemma srv_le_add {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : srv S j t ≤ srv S j s + (t - s) := by
  rw [srv_split S j hs hst]; linarith [piece_le S j hst]

lemma srv_of_nonpos {t : ℝ} (ht : t ≤ 0) : srv S j t = 0 := by
  unfold srv
  rw [Ico_eq_empty (by linarith), inter_empty, measure_empty, ENNReal.toReal_zero]

lemma srv_eq_zero (a : ι → ℝ) (hS : ∀ u, S u = some j → a j ≤ u) {t : ℝ} (ht : t ≤ a j) :
    srv S j t = 0 := by
  unfold srv
  have : {u : ℝ | S u = some j} ∩ Ico 0 t = ∅ := by
    ext u; simp only [mem_inter_iff, mem_setOf_eq, mem_Ico, mem_empty_iff_false, iff_false, not_and]
    intro h1 _ h3; linarith [hS u h1]
  rw [this, measure_empty, ENNReal.toReal_zero]

/-- feasibility caps the service at the requirement. -/
lemma srv_le_r (a r : ι → ℝ) (hr : 0 < r j) (hfeas : ∀ t, S t = some j → pres a r S j t) (t : ℝ) :
    srv S j t ≤ r j := by
  by_contra hlt
  push_neg at hlt
  have ht0 : 0 ≤ t := by
    by_contra h; push_neg at h; rw [srv_of_nonpos S j h.le] at hlt; linarith
  set T : Set ℝ := {s | s ∈ Icc 0 t ∧ srv S j s < r j} with hT
  have h0T : (0:ℝ) ∈ T := ⟨⟨le_rfl, ht0⟩, by rw [srv_of_nonpos S j le_rfl]; exact hr⟩
  have hbdd : BddAbove T := ⟨t, fun s hs => hs.1.2⟩
  set d := sSup T
  have hd0 : 0 ≤ d := le_csSup hbdd h0T
  have hdt : d ≤ t := csSup_le ⟨0, h0T⟩ fun s hs => hs.1.2
  -- srv d ≤ r j
  have hdr : srv S j d ≤ r j := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨s, hsT, hs⟩ := exists_lt_of_lt_csSup ⟨0, h0T⟩ (show d - ε < d by linarith)
    have hsd : s ≤ d := le_csSup hbdd hsT
    have := srv_le_add S j hsT.1.1 hsd
    linarith [hsT.2]
  -- no service in (d, t]
  have hnone : {u : ℝ | S u = some j} ∩ Ico d t ⊆ {d} := by
    intro u ⟨hu, hu1, hu2⟩
    by_contra hne
    have hdu : d < u := lt_of_le_of_ne hu1 (Ne.symm hne)
    have hp := (hfeas u hu).2
    have : u ∈ T := ⟨⟨by linarith, hu2.le⟩, hp⟩
    linarith [le_csSup hbdd this]
  have hz : (volume ({u : ℝ | S u = some j} ∩ Ico d t)).toReal = 0 := by
    have : volume ({u : ℝ | S u = some j} ∩ Ico d t) = 0 :=
      measure_mono_null hnone (Real.volume_singleton)
    rw [this, ENNReal.toReal_zero]
  have := srv_split S j hd0 hdt
  linarith

end srv

/-! ## work input -/

section wIn
variable (a r : ι → ℝ)

lemma wIn_self (s : ℝ) : wIn a r s s = 0 := by
  unfold wIn
  have h : ∀ j, Set.indicator {j : ι | s ≤ a j ∧ a j < s} r j = 0 := fun j =>
    indicator_of_notMem (fun hh => lt_irrefl _ (lt_of_le_of_lt hh.1 hh.2)) _
  simp [h]

lemma wIn_eq_sum {s t : ℝ} (F : Finset ι) (hF : ∀ j, a j < t → j ∈ F) :
    wIn a r s t = ∑ j ∈ F, Set.indicator {j : ι | s ≤ a j ∧ a j < t} r j := by
  unfold wIn
  refine tsum_eq_sum fun j hj => ?_
  rw [Set.indicator_of_notMem]
  intro h; exact hj (hF j h.2)

lemma wIn_add (hD : DGood a r) {u v w : ℝ} (huv : u ≤ v) (hvw : v ≤ w) :
    wIn a r u w = wIn a r u v + wIn a r v w := by
  classical
  set F := (hD.fin w).toFinset
  have hF : ∀ j, a j < w → j ∈ F := fun j h => (hD.fin w).mem_toFinset.2 (le_of_lt h)
  rw [wIn_eq_sum a r F hF, wIn_eq_sum a r F (fun j h => hF j (by linarith)),
    wIn_eq_sum a r F hF, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases lt_or_ge (a j) v with h | h
  · rw [indicator_of_notMem (show j ∉ {j : ι | v ≤ a j ∧ a j < w} from
      fun hh => absurd hh.1 (not_le.2 h)), add_zero]
    by_cases hu : u ≤ a j
    · rw [indicator_of_mem (show j ∈ {j : ι | u ≤ a j ∧ a j < w} from ⟨hu, by linarith⟩),
        indicator_of_mem (show j ∈ {j : ι | u ≤ a j ∧ a j < v} from ⟨hu, h⟩)]
    · rw [indicator_of_notMem (show j ∉ {j : ι | u ≤ a j ∧ a j < w} from fun hh => hu hh.1),
        indicator_of_notMem (show j ∉ {j : ι | u ≤ a j ∧ a j < v} from fun hh => hu hh.1)]
  · rw [indicator_of_notMem (show j ∉ {j : ι | u ≤ a j ∧ a j < v} from
      fun hh => absurd hh.2 (not_lt.2 h)), zero_add]
    by_cases hw : a j < w
    · rw [indicator_of_mem (show j ∈ {j : ι | u ≤ a j ∧ a j < w} from ⟨by linarith, hw⟩),
        indicator_of_mem (show j ∈ {j : ι | v ≤ a j ∧ a j < w} from ⟨h, hw⟩)]
    · rw [indicator_of_notMem (show j ∉ {j : ι | u ≤ a j ∧ a j < w} from fun hh => hw hh.2),
        indicator_of_notMem (show j ∉ {j : ι | v ≤ a j ∧ a j < w} from fun hh => hw hh.2)]

lemma wIn_nonneg (hD : DGood a r) (s t : ℝ) : 0 ≤ wIn a r s t :=
  tsum_nonneg fun j => Set.indicator_nonneg (fun j _ => (hD.rpos j).le) j

lemma wIn_mono (hD : DGood a r) {u v w : ℝ} (huv : u ≤ v) (hvw : v ≤ w) :
    wIn a r u v ≤ wIn a r u w := by
  rw [wIn_add a r hD huv hvw]; linarith [wIn_nonneg a r hD v w]

lemma le_wIn (hD : DGood a r) {s t : ℝ} {j : ι} (h1 : s ≤ a j) (h2 : a j < t) :
    r j ≤ wIn a r s t := by
  classical
  set F := (hD.fin t).toFinset
  have hF : ∀ j, a j < t → j ∈ F := fun j h => (hD.fin t).mem_toFinset.2 (le_of_lt h)
  rw [wIn_eq_sum a r F hF]
  have := Finset.single_le_sum (f := fun j => Set.indicator {j : ι | s ≤ a j ∧ a j < t} r j)
    (fun j _ => Set.indicator_nonneg (fun j _ => (hD.rpos j).le) j) (hF j h2)
  simpa [Set.indicator_of_mem (show j ∈ {j : ι | s ≤ a j ∧ a j < t} from ⟨h1, h2⟩)] using this

end wIn


/-! ## busy-period locality -/

section core
variable {a r : ι → ℝ} {S : ℝ → Option ι}

/-- at an idle point all earlier jobs are done (work conservation). -/
theorem done_of_idlePt (hD : DGood a r) (hS : SGood a r S) {t : ℝ} (hI : IdlePt a r t) :
    ∀ j, a j < t → r j ≤ srv S j t := by
  classical
  intro j hjt
  have ht0 : 0 < t := lt_trans (hD.apos j) hjt
  set I : Set ℝ := {s | s < t ∧ ∀ j, ¬ pres a r S j s} with hIdef
  have h0I : (0:ℝ) ∈ I := ⟨ht0, fun j' hp => absurd hp.1 (not_le.2 (hD.apos j'))⟩
  have hbdd : BddAbove I := ⟨t, fun s hs => hs.1.le⟩
  set s0 := sSup I with hs0
  have hs00 : 0 ≤ s0 := le_csSup hbdd h0I
  have hs0t : s0 ≤ t := csSup_le ⟨0, h0I⟩ fun s hs => hs.1.le
  set F : Finset ι := ((hD.fin t).toFinset).filter (fun j => a j < t) with hF
  have memF : ∀ j', j' ∈ F ↔ a j' < t := fun j' => by
    simp only [hF, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  have busy : Ioo s0 t ⊆ ⋃ j' ∈ F, ({u : ℝ | S u = some j'} ∩ Ico s0 t) := by
    intro u ⟨hu1, hu2⟩
    have hnI : u ∉ I := fun h => absurd (le_csSup hbdd h) (not_le.2 hu1)
    have : ∃ j', pres a r S j' u := by
      by_contra hc; push_neg at hc; exact hnI ⟨hu2, hc⟩
    obtain ⟨j', hj'⟩ := this
    have hne : S u ≠ none := fun h => ((hS.idle u).1 h) j' hj'
    obtain ⟨j'', hj''⟩ := Option.ne_none_iff_exists'.1 hne
    have := (hS.feas u j'' hj'').1
    simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq, mem_Ico, exists_prop]
    exact ⟨j'', (memF j'').2 (by linarith), hj'', hu1.le, hu2⟩
  have hsum_piece : t - s0 ≤ ∑ j' ∈ F, (volume ({u : ℝ | S u = some j'} ∩ Ico s0 t)).toReal := by
    rw [← ENNReal.toReal_sum (fun j' _ => vol_Ico_ne_top _ _ _),
      ← measure_biUnion_finset₀ ?_ ?_]
    · have h1 := measure_mono (μ := volume) busy
      rw [Real.volume_Ioo] at h1
      have h2 := ENNReal.toReal_mono ?_ h1
      · rwa [ENNReal.toReal_ofReal (by linarith)] at h2
      · exact ne_top_of_le_ne_top (by simp : volume (Ico s0 t) ≠ ⊤)
          (measure_mono (iUnion₂_subset fun _ _ => inter_subset_right))
    · intro x _ y _ hxy
      show AEDisjoint volume _ _
      exact Disjoint.aedisjoint (Disjoint.mono inter_subset_left inter_subset_left
        (Set.disjoint_left.2 fun u hx hy => hxy (Option.some_injective _ (hx.symm.trans hy))))
    · intro j' _; exact (hS.meas j').inter measurableSet_Ico.nullMeasurableSet
  have hold : ∀ j', a j' < s0 → r j' ≤ srv S j' s0 := by
    intro j' hj'
    obtain ⟨s, hsI, hs⟩ := exists_lt_of_lt_csSup ⟨0, h0I⟩ hj'
    have hnp := hsI.2 j'
    have : r j' ≤ srv S j' s := by
      by_contra hc; push_neg at hc; exact hnp ⟨hs.le, hc⟩
    exact this.trans (srv_mono S j' (le_csSup hbdd hsI))
  have hnew : ∀ j', s0 ≤ a j' → srv S j' s0 = 0 := fun j' h =>
    srv_eq_zero S j' a (fun u hu => (hS.feas u j' hu).1) h
  have hsplit : ∀ j' ∈ F, srv S j' t =
      srv S j' s0 + (volume ({u : ℝ | S u = some j'} ∩ Ico s0 t)).toReal :=
    fun j' _ => srv_split S j' hs00 hs0t
  have hW : wIn a r s0 t = ∑ j' ∈ F.filter (fun j' => s0 ≤ a j'), r j' := by
    rw [wIn_eq_sum a r F (fun j' h => (memF j').2 h), Finset.sum_filter (s := F)]
    refine Finset.sum_congr rfl fun j' hj' => ?_
    have := (memF j').1 hj'
    by_cases h : s0 ≤ a j'
    · rw [if_pos h, indicator_of_mem (show j' ∈ {j : ι | s0 ≤ a j ∧ a j < t} from ⟨h, this⟩)]
    · rw [if_neg h, indicator_of_notMem
        (show j' ∉ {j : ι | s0 ≤ a j ∧ a j < t} from fun hh => h hh.1)]
  have hIdle := hI s0 hs0t
  have hle : ∑ j' ∈ F, r j' ≤ ∑ j' ∈ F, srv S j' t := by
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
      ← Finset.sum_filter_add_sum_filter_not F (fun j' => a j' < s0) (fun j' => r j'),
      ← Finset.sum_filter_add_sum_filter_not F (fun j' => a j' < s0) (fun j' => srv S j' s0)]
    have e1 : ∑ j' ∈ F.filter (fun j' => ¬ a j' < s0), srv S j' s0 = 0 :=
      Finset.sum_eq_zero fun j' hj' => hnew j' (not_lt.1 (Finset.mem_filter.1 hj').2)
    have e2 : ∑ j' ∈ F.filter (fun j' => ¬ a j' < s0), r j' = wIn a r s0 t := by
      rw [hW]; exact Finset.sum_congr (Finset.filter_congr fun x _ => not_lt) fun _ _ => rfl
    have e3 : ∑ j' ∈ F.filter (fun j' => a j' < s0), r j' ≤
        ∑ j' ∈ F.filter (fun j' => a j' < s0), srv S j' s0 :=
      Finset.sum_le_sum fun j' hj' => hold j' (Finset.mem_filter.1 hj').2
    linarith
  have hcap : ∀ j' ∈ F, srv S j' t ≤ r j' := fun j' _ =>
    srv_le_r S j' a r (hD.rpos j') (fun u hu => hS.feas u j' hu) t
  by_contra hc
  push_neg at hc
  have := Finset.sum_lt_sum hcap ⟨j, (memF j).2 hjt, hc⟩
  linarith

/-- leaving a busy period produces an idle point. -/
theorem exit_of_not_inB (hD : DGood a r) {j0 : ι} (hB : BPS a r j0) {t : ℝ} (ht : a j0 ≤ t)
    (hn : ¬ InB a r j0 t) :
    ∃ s, a j0 < s ∧ s ≤ t ∧ IdlePt a r s ∧ wIn a r (a j0) s ≤ s - a j0 := by
  have hZ : ∃ s ∈ Ioc (a j0) t, wIn a r (a j0) s ≤ s - a j0 := by
    by_contra hc; push_neg at hc; exact hn ⟨ht, hc⟩
  set Z : Set ℝ := {s | s ∈ Ioc (a j0) t ∧ wIn a r (a j0) s ≤ s - a j0} with hZdef
  have hne : Z.Nonempty := let ⟨s, h1, h2⟩ := hZ; ⟨s, h1, h2⟩
  have hlow : ∀ z ∈ Z, a j0 + r j0 ≤ z := fun z hz => by
    have := le_wIn a r hD (le_refl (a j0)) hz.1.1
    linarith [hz.2]
  have hbdd : BddBelow Z := ⟨a j0 + r j0, hlow⟩
  set s := sInf Z with hsdef
  have hs1 : a j0 + r j0 ≤ s := le_csInf hne hlow
  have hr := hD.rpos j0
  obtain ⟨z0, hz0⟩ := hne
  have hst : s ≤ t := (csInf_le hbdd hz0).trans hz0.1.2
  have hg : wIn a r (a j0) s ≤ s - a j0 := by
    have : ∀ z ∈ Z, wIn a r (a j0) s + a j0 ≤ z := fun z hz => by
      have := wIn_mono a r hD (show a j0 ≤ s by linarith) (csInf_le hbdd hz)
      linarith [hz.2]
    have := le_csInf ⟨z0, hz0⟩ this
    linarith
  refine ⟨s, by linarith, hst, fun s'' hs'' => ?_, hg⟩
  rcases le_or_gt s'' (a j0) with h | h
  · rw [wIn_add a r hD h (by linarith)]
    linarith [hB s'' h]
  · rcases eq_or_lt_of_le hs'' with h' | h'
    · rw [h', wIn_self]; linarith
    · have hnZ : s'' ∉ Z := fun hz => absurd (csInf_le hbdd hz) (not_le.2 h')
      have hlt : s'' - a j0 < wIn a r (a j0) s'' := by
        by_contra hc; push_neg at hc; exact hnZ ⟨⟨h, by linarith⟩, hc⟩
      have := wIn_add a r hD h.le h'.le
      linarith

theorem done_of_not_inB (hD : DGood a r) (hS : SGood a r S) {j0 j : ι} (hB : BPS a r j0)
    (hj : InB a r j0 (a j)) {t : ℝ} (ht : a j0 ≤ t) (hn : ¬ InB a r j0 t) :
    r j ≤ srv S j t := by
  obtain ⟨s, hs0, hst, hI, hg⟩ := exit_of_not_inB hD hB ht hn
  have hjs : a j < s := by
    by_contra hc; push_neg at hc
    have := hj.2 s ⟨hs0, hc⟩
    linarith
  exact (done_of_idlePt hD hS hI j hjs).trans (srv_mono S j hst)

theorem inB_of_pres (hD : DGood a r) (hS : SGood a r S) {j0 j : ι} (hB : BPS a r j0)
    (hj : InB a r j0 (a j)) {t : ℝ} (hp : pres a r S j t) : InB a r j0 t := by
  by_contra hn
  have := done_of_not_inB hD hS hB hj (hj.1.trans hp.1) hn
  linarith [hp.2]

theorem inB_of_served (hD : DGood a r) (hS : SGood a r S) {j0 j : ι} (hB : BPS a r j0)
    (hj : InB a r j0 (a j)) {t : ℝ} (h : S t = some j) : InB a r j0 t :=
  inB_of_pres hD hS hB hj (hS.feas t j h)

theorem eq_of_two {j0 j1 : ι} {t : ℝ} (hB0 : BPS a r j0) (hB1 : BPS a r j1)
    (h0 : InB a r j0 t) (h1 : InB a r j1 t) : a j0 = a j1 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := h0.2 (a j1) ⟨h, h1.1⟩
    have := hB1 (a j0) h.le
    linarith
  · have := h1.2 (a j0) ⟨h, h0.1⟩
    have := hB0 (a j1) h.le
    linarith

theorem exists_opener (hD : DGood a r) (j : ι) : ∃ j0, BPS a r j0 ∧ InB a r j0 (a j) := by
  classical
  set F := (hD.fin (a j)).toFinset with hFdef
  have memF : ∀ j', j' ∈ F ↔ a j' ≤ a j := fun j' => by simp [F]
  have hjF : j ∈ F := (memF j).2 le_rfl
  obtain ⟨j1, hj1F, hj1min⟩ := F.exists_min_image a ⟨j, hjF⟩
  have hB1 : BPS a r j1 := fun s hs => by
    have : wIn a r s (a j1) = 0 := by
      unfold wIn
      refine (tsum_congr fun j' => indicator_of_notMem (fun hh => ?_) _).trans tsum_zero
      have := hj1min j' ((memF j').2 (by linarith [hh.2, (memF j1).1 hj1F]))
      linarith [hh.2]
    rw [this]; linarith
  set G := F.filter (fun j' => BPS a r j') with hGdef
  have hGne : G.Nonempty := ⟨j1, Finset.mem_filter.2 ⟨hj1F, hB1⟩⟩
  obtain ⟨j0, hj0G, hj0max⟩ := G.exists_max_image a hGne
  have hj0F := (Finset.mem_filter.1 hj0G).1
  have hB0 := (Finset.mem_filter.1 hj0G).2
  refine ⟨j0, hB0, ?_⟩
  by_contra hn
  obtain ⟨s, hs0, hst, hI, _⟩ := exit_of_not_inB hD hB0 ((memF j0).1 hj0F) hn
  set H := F.filter (fun j' => s ≤ a j') with hHdef
  have hHne : H.Nonempty := ⟨j, Finset.mem_filter.2 ⟨hjF, hst⟩⟩
  obtain ⟨j', hj'H, hj'min⟩ := H.exists_min_image a hHne
  have hj'F := (Finset.mem_filter.1 hj'H).1
  have hsj' := (Finset.mem_filter.1 hj'H).2
  have gap : ∀ s', s ≤ s' → wIn a r s' (a j') = 0 := by
    intro s' hs'
    unfold wIn
    refine (tsum_congr fun k => indicator_of_notMem (fun hh => ?_) _).trans tsum_zero
    have hkF : k ∈ F := (memF k).2 (by linarith [hh.2, (memF j').1 hj'F])
    have := hj'min k (Finset.mem_filter.2 ⟨hkF, by linarith [hh.1]⟩)
    linarith [hh.2]
  have hB' : BPS a r j' := fun s'' hs'' => by
    rcases le_or_gt s'' s with h | h
    · rw [wIn_add a r hD h hsj', gap s le_rfl, add_zero]
      linarith [hI s'' h]
    · rw [gap s'' h.le]; linarith
  have := hj0max j' (Finset.mem_filter.2 ⟨hj'F, hB'⟩)
  linarith

end core

/-! ## generic mixing over busy periods -/

section mix
variable {a r : ι → ℝ} {K : Type*}

structure MixSpec (a r : ι → ℝ) (Sk : K → ℝ → Option ι) (τ : ι → K) (M : ℝ → Option ι) :
    Prop where
  on : ∀ t j0, BPS a r j0 → InB a r j0 t → M t = Sk (τ j0) t
  off : ∀ t, (∀ j0, BPS a r j0 → ¬ InB a r j0 t) → M t = none

variable {Sk : K → ℝ → Option ι} {τ : ι → K} {M : ℝ → Option ι}

theorem mix_set (hD : DGood a r) (hinj : Function.Injective a) (hSk : ∀ k, SGood a r (Sk k))
    (hM : MixSpec a r Sk τ M) {j j0 : ι} (hB : BPS a r j0) (hj : InB a r j0 (a j)) :
    {s : ℝ | M s = some j} = {s : ℝ | Sk (τ j0) s = some j} := by
  ext s
  simp only [mem_setOf_eq]
  constructor
  · intro h
    by_cases hex : ∃ j1, BPS a r j1 ∧ InB a r j1 s
    · obtain ⟨j1, hB1, hI1⟩ := hex
      rw [hM.on s j1 hB1 hI1] at h
      have := inB_of_served hD (hSk (τ j1)) hB hj h
      rw [hinj (eq_of_two hB hB1 this hI1)]; exact h
    · push_neg at hex
      rw [hM.off s hex] at h; exact absurd h (by simp)
  · intro h
    rw [hM.on s j0 hB (inB_of_served hD (hSk (τ j0)) hB hj h)]; exact h

theorem mix_srv (hD : DGood a r) (hinj : Function.Injective a) (hSk : ∀ k, SGood a r (Sk k))
    (hM : MixSpec a r Sk τ M) {j j0 : ι} (hB : BPS a r j0) (hj : InB a r j0 (a j)) :
    srv M j = srv (Sk (τ j0)) j := by
  funext t; unfold srv; rw [mix_set hD hinj hSk hM hB hj]

theorem mix_pres (hD : DGood a r) (hinj : Function.Injective a) (hSk : ∀ k, SGood a r (Sk k))
    (hM : MixSpec a r Sk τ M) {j j0 : ι} (hB : BPS a r j0) (hj : InB a r j0 (a j)) (t : ℝ) :
    pres a r M j t ↔ pres a r (Sk (τ j0)) j t := by
  unfold pres; rw [mix_srv hD hinj hSk hM hB hj]

theorem mix_good (hD : DGood a r) (hinj : Function.Injective a) (hSk : ∀ k, SGood a r (Sk k))
    (hM : MixSpec a r Sk τ M) : SGood a r M where
  feas t j h := by
    obtain ⟨j0, hB, hj⟩ := exists_opener hD j
    have h' : Sk (τ j0) t = some j := (Set.ext_iff.1 (mix_set hD hinj hSk hM hB hj) t).1 h
    exact (mix_pres hD hinj hSk hM hB hj t).2 ((hSk (τ j0)).feas t j h')
  idle t := by
    constructor
    · intro hnone j hp
      obtain ⟨j0, hB, hj⟩ := exists_opener hD j
      have hpk := (mix_pres hD hinj hSk hM hB hj t).1 hp
      have hI := inB_of_pres hD (hSk (τ j0)) hB hj hpk
      rw [hM.on t j0 hB hI] at hnone
      exact ((hSk (τ j0)).idle t).1 hnone j hpk
    · intro hall
      by_cases hex : ∃ j0, BPS a r j0 ∧ InB a r j0 t
      · obtain ⟨j0, hB, hI⟩ := hex
        rw [hM.on t j0 hB hI]
        refine ((hSk (τ j0)).idle t).2 fun j hpk => ?_
        obtain ⟨j1, hB1, hj1⟩ := exists_opener hD j
        have hI1 := inB_of_pres hD (hSk (τ j0)) hB1 hj1 hpk
        have h10 : j1 = j0 := hinj (eq_of_two hB1 hB hI1 hI)
        subst h10
        exact hall j ((mix_pres hD hinj hSk hM hB1 hj1 t).2 hpk)
      · push_neg at hex; exact hM.off t hex
  meas j := by
    obtain ⟨j0, hB, hj⟩ := exists_opener hD j
    rw [mix_set hD hinj hSk hM hB hj]; exact (hSk _).meas j

end mix

end CMX


/-! # 27b64375 seed layer (Mathlib only): the seed array `c : ι → ℕ → E` under
`C = infinitePi (fun _ => infinitePi (fun _ => η))`: dropping the first seed of every job is
measure preserving, and the first seeds are independent of the dropped array. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CMY
open MeasureTheory ProbabilityTheory Set

variable {ι : Type*} [Countable ι] {E : Type*} [MeasurableSpace E] (η : Measure E)
  [IsProbabilityMeasure η]

/-- the seed law `C`. -/
noncomputable def C : Measure (ι → ℕ → E) :=
  Measure.infinitePi fun _ : ι => Measure.infinitePi fun _ : ℕ => η

instance : IsProbabilityMeasure (C (ι := ι) η) := by unfold C; infer_instance

/-- drop the first seed of every job. -/
def sig (c : ι → ℕ → E) : ι → ℕ → E := fun j ℓ => c j (ℓ + 1)

/-- the first seed of every job. -/
def hd (c : ι → ℕ → E) : ι → E := fun j => c j 0

lemma measurable_sig : Measurable (sig (ι := ι) (E := E)) :=
  measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun ℓ =>
    (measurable_pi_apply (ℓ + 1)).comp (measurable_pi_apply j)

lemma measurable_hd : Measurable (hd (ι := ι) (E := E)) :=
  measurable_pi_lambda _ fun j => (measurable_pi_apply 0).comp (measurable_pi_apply j)

def consN {α : Type*} (a : α) (f : ℕ → α) : ℕ → α
  | 0 => a
  | n + 1 => f n

@[simp] lemma consN_zero {α : Type*} (a : α) (f : ℕ → α) : consN a f 0 = a := rfl
@[simp] lemma consN_succ {α : Type*} (a : α) (f : ℕ → α) (n : ℕ) : consN a f (n + 1) = f n := rfl

lemma measurable_consN {α : Type*} [MeasurableSpace α] :
    Measurable (fun p : α × (ℕ → α) => consN p.1 p.2) := by
  refine measurable_pi_lambda _ fun n => ?_
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

lemma prod_split_zero {M : Type*} [CommMonoid M] (s : Finset ℕ) (g : ℕ → M) :
    ∏ i ∈ s, g i = (if 0 ∈ s then g 0 else 1) *
      ∏ n ∈ s.preimage Nat.succ Nat.succ_injective.injOn, g (n + 1) := by
  classical
  have key : ∏ n ∈ s.preimage Nat.succ Nat.succ_injective.injOn, g (n + 1)
      = ∏ i ∈ s.erase 0, g i := by
    refine Finset.prod_nbij' (fun n => n + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_preimage] at hn
      simp [hn]
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_erase] at hi
      simp only [Finset.mem_coe, Finset.mem_preimage]
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi.1)]; exact hi.2
    · intro n _; simp
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_erase] at hi
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hi.1)
    · intro n _; rfl
  rw [key]
  by_cases h0 : 0 ∈ s
  · rw [if_pos h0, Finset.mul_prod_erase s g h0]
  · rw [if_neg h0, one_mul, Finset.erase_eq_of_notMem h0]

theorem map_consN :
    (η.prod (Measure.infinitePi fun _ : ℕ => η)).map (fun p : E × (ℕ → E) => consN p.1 p.2)
      = Measure.infinitePi fun _ : ℕ => η := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  rw [Measure.map_apply measurable_consN (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hpre : (fun p : E × (ℕ → E) => consN p.1 p.2) ⁻¹' (Set.pi ↑s t) =
      (if 0 ∈ s then t 0 else univ) ×ˢ
        Set.pi ↑(s.preimage Nat.succ Nat.succ_injective.injOn) (fun n => t (n + 1)) := by
    ext ⟨a, f⟩
    simp only [mem_preimage, mem_pi, Finset.mem_coe, mem_prod, Finset.mem_preimage]
    constructor
    · intro h
      refine ⟨?_, fun n hn => h (n + 1) hn⟩
      split_ifs with h0
      · exact h 0 h0
      · trivial
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => simpa [hi] using h0
      | succ n => exact h1 n hi
  rw [hpre, Measure.prod_prod, Measure.infinitePi_pi _ (fun i _ => ht (i + 1)), prod_split_zero s]
  congr 1
  split_ifs <;> simp

/-- dropping the first seed of one sequence preserves the i.i.d. law. -/
theorem map_tail :
    (Measure.infinitePi fun _ : ℕ => η).map (fun v : ℕ → E => fun ℓ => v (ℓ + 1))
      = Measure.infinitePi fun _ : ℕ => η := by
  have hm : Measurable (fun v : ℕ → E => fun ℓ => v (ℓ + 1)) :=
    measurable_pi_lambda _ fun ℓ => measurable_pi_apply (ℓ + 1)
  conv_lhs => rw [← map_consN η]
  rw [Measure.map_map hm measurable_consN]
  have : ((fun v : ℕ → E => fun ℓ => v (ℓ + 1)) ∘ fun p : E × (ℕ → E) => consN p.1 p.2)
      = Prod.snd := by funext p; rfl
  rw [this, Measure.map_snd_prod, measure_univ, one_smul]

theorem mp_sig : MeasurePreserving (sig (ι := ι) (E := E)) (C η) (C η) := by
  refine ⟨measurable_sig, ?_⟩
  unfold C
  have := Measure.infinitePi_map_pi (μ := fun _ : ι => Measure.infinitePi fun _ : ℕ => η)
    (f := fun _ (v : ℕ → E) => fun ℓ => v (ℓ + 1))
    (fun _ => measurable_pi_lambda _ fun ℓ => measurable_pi_apply (ℓ + 1))
  simp only [map_tail] at this
  exact this

theorem map_hd_eval (j : ι) : (C η).map (fun c : ι → ℕ → E => c j 0) = η := by
  unfold C
  have h1 := (measurePreserving_eval_infinitePi (fun _ : ι => Measure.infinitePi fun _ : ℕ => η) j)
  have h2 := (measurePreserving_eval_infinitePi (fun _ : ℕ => η) 0)
  exact (h2.comp h1).map_eq

theorem indep_hd_sig : IndepFun (hd (ι := ι) (E := E)) (sig (ι := ι) (E := E)) (C η) := by
  have h := iIndepFun_uncurry_infinitePi' (X := fun (_ : ι) (_ : ℕ) (x : E) => x)
    (fun _ _ => η) (fun _ _ => measurable_id)
  rw [iIndepFun_iff_iIndep] at h
  have hle : ∀ p : ι × ℕ, MeasurableSpace.comap (fun c : ι → ℕ → E => c p.1 p.2)
      (inferInstance : MeasurableSpace E) ≤ MeasurableSpace.pi :=
    fun p => (show Measurable (fun c : ι → ℕ → E => c p.1 p.2) from
      (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)).comap_le
  have hI := indep_iSup_of_disjoint hle h (S := {p : ι × ℕ | p.2 = 0}) (T := {p | p.2 ≠ 0})
    (Set.disjoint_left.2 fun p h1 h2 => h2 h1)
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hI ?_) ?_
  · simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    refine iSup_le fun j => ?_
    exact le_iSup₂ (f := fun (p : ι × ℕ) (_ : p ∈ {p : ι × ℕ | p.2 = 0}) =>
      MeasurableSpace.comap (fun c : ι → ℕ → E => c p.1 p.2) (inferInstance : MeasurableSpace E))
      (j, 0) rfl
  · simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    refine iSup_le fun j => iSup_le fun ℓ => ?_
    exact le_iSup₂ (f := fun (p : ι × ℕ) (_ : p ∈ {p : ι × ℕ | p.2 ≠ 0}) =>
      MeasurableSpace.comap (fun c : ι → ℕ → E => c p.1 p.2) (inferInstance : MeasurableSpace E))
      (j, ℓ + 1) (Nat.succ_ne_zero ℓ)

/-- the key product formula: for `g` of one first seed and `h` of the dropped array. -/
theorem integral_hd_mul_sig (j : ι) {g : E → ℝ} (hg : Measurable g) {h : (ι → ℕ → E) → ℝ}
    (hh : AEStronglyMeasurable h (C η)) :
    ∫ c, g (c j 0) * h (sig c) ∂(C η) = (∫ x, g x ∂η) * ∫ c, h c ∂(C η) := by
  have hind : IndepFun (fun c : ι → ℕ → E => c j 0) (sig (ι := ι) (E := E)) (C η) := by
    have := (indep_hd_sig η (ι := ι)).comp (measurable_pi_apply j) measurable_id
    exact this
  have h1 := hind.integral_fun_comp_mul_comp (f := g) (g := h)
    ((measurable_pi_apply 0).comp (measurable_pi_apply j)).aemeasurable
    measurable_sig.aemeasurable
    (by rw [map_hd_eval]; exact hg.aestronglyMeasurable)
    (by rw [(mp_sig η).map_eq]; exact hh)
  rw [h1, ← integral_map measurable_sig.aemeasurable (by rw [(mp_sig η).map_eq]; exact hh),
    (mp_sig η).map_eq,
    ← integral_map (φ := fun c : ι → ℕ → E => c j 0)
      ((measurable_pi_apply 0).comp (measurable_pi_apply j)).aemeasurable
      (by rw [map_hd_eval]; exact hg.aestronglyMeasurable), map_hd_eval]

end CMY


/-! # 27b64375 arrival layer (Mathlib only): under independent exponential interarrival times,
arrival epochs of distinct jobs are almost surely distinct (no ties). -/

set_option autoImplicit false

namespace CMA
open MeasureTheory ProbabilityTheory Set Finset

/-- independent `U`, `V` with an atomless law of `U` almost never coincide. -/
theorem ae_ne_of_indep {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {U V : Ω → ℝ} (hU : Measurable U) (hV : Measurable V) (hind : IndepFun U V μ)
    (hat : ∀ v : ℝ, (μ.map U) {v} = 0) : ∀ᵐ ω ∂μ, U ω ≠ V ω := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := measurableSet_diagonal
  have h1 : μ {ω | U ω = V ω} = (μ.map fun ω => (U ω, V ω)) {p : ℝ × ℝ | p.1 = p.2} := by
    rw [Measure.map_apply (hU.prodMk hV) hmeas]; rfl
  rw [h1, (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 hind,
    Measure.prod_apply_symm hmeas]
  refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun v => ?_)
  have : (fun x : ℝ => (x, v)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {v} := by ext x; simp
  simp only [this, hat v, Pi.zero_apply]

lemma expMeasure_singleton (r v : ℝ) : expMeasure r {v} = 0 := by
  unfold expMeasure gammaMeasure
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

lemma ae_pos_expMeasure (r : ℝ) : ∀ᵐ y ∂(expMeasure r), 0 < y := by
  rw [ae_iff]
  simp only [not_lt]
  unfold expMeasure gammaMeasure
  show (volume.withDensity (gammaPDF 1 r)) (Set.Iic 0) = 0
  rw [withDensity_apply _ measurableSet_Iic, setLIntegral_congr Iio_ae_eq_Iic.symm]
  exact lintegral_gammaPDF_of_nonpos le_rfl

variable {M : ℕ}

/-- arrival epoch of job `(i, n)` from interarrival times `x`. -/
def arr (x : Fin M × ℕ → ℝ) (j : Fin M × ℕ) : ℝ := ∑ m ∈ range (j.2 + 1), x (j.1, m)

/-- different classes: almost surely no tie. -/
theorem ae_arr_ne (lam : Fin M → ℝ) (hlam : ∀ i, 0 < lam i) {i i' : Fin M} (hii : i ≠ i')
    (n n' : ℕ) :
    ∀ᵐ x ∂(Measure.infinitePi fun j : Fin M × ℕ => expMeasure (lam j.1)),
      arr x (i, n) ≠ arr x (i', n') := by
  classical
  have : ∀ j : Fin M × ℕ, IsProbabilityMeasure (expMeasure (lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (hlam j.1)
  set μ := Measure.infinitePi fun j : Fin M × ℕ => expMeasure (lam j.1)
  have hall : iIndepFun (fun (j : Fin M × ℕ) (x : Fin M × ℕ → ℝ) => x j) μ :=
    iIndepFun_infinitePi (X := fun _ (y : ℝ) => y) (fun _ => measurable_id)
  set S : Finset (Fin M × ℕ) := {(i, 0)}
  set T : Finset (Fin M × ℕ) :=
    ((Finset.Ico 1 (n + 1)).image fun m => (i, m)) ∪ ((range (n' + 1)).image fun m => (i', m))
  have hST : Disjoint S T := by
    rw [Finset.disjoint_singleton_left]
    simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_Ico, Finset.mem_range,
      Prod.mk.injEq, not_or, not_exists, not_and]
    exact ⟨fun m hm _ hm0 => by omega, fun m _ h => absurd h.symm hii⟩
  have hind := hall.indepFun_finset S T hST (fun j => measurable_pi_apply j)
  -- U = x (i,0), V = arr (i',n') - sum_{m=1}^{n} x (i,m)
  set U : (S → ℝ) → ℝ := fun y => y ⟨(i, 0), Finset.mem_singleton_self _⟩
  set V : (T → ℝ) → ℝ := fun y =>
    (∑ m ∈ (range (n' + 1)).attach, y ⟨(i', m.1), Finset.mem_union_right _
        (Finset.mem_image.2 ⟨m.1, m.2, rfl⟩)⟩)
      - ∑ m ∈ (Finset.Ico 1 (n + 1)).attach, y ⟨(i, m.1), Finset.mem_union_left _
        (Finset.mem_image.2 ⟨m.1, m.2, rfl⟩)⟩
  have hUm : Measurable U := measurable_pi_apply _
  have hVm : Measurable V := by
    refine Measurable.sub (Finset.measurable_sum _ fun m _ => measurable_pi_apply _)
      (Finset.measurable_sum _ fun m _ => measurable_pi_apply _)
  have hind2 := hind.comp hUm hVm
  have hXm : Measurable fun x : Fin M × ℕ → ℝ => U fun k : S => x k :=
    hUm.comp (measurable_pi_lambda (fun (x : Fin M × ℕ → ℝ) (k : S) => x k)
      fun k => measurable_pi_apply _)
  have hYm : Measurable fun x : Fin M × ℕ → ℝ => V fun k : T => x k :=
    hVm.comp (measurable_pi_lambda (fun (x : Fin M × ℕ → ℝ) (k : T) => x k)
      fun k => measurable_pi_apply _)
  have hat : ∀ v : ℝ, (μ.map fun x : Fin M × ℕ → ℝ => U fun k : S => x k) {v} = 0 := by
    intro v
    have : (fun x : Fin M × ℕ → ℝ => U fun k : S => x k) = fun x => x (i, 0) := rfl
    rw [this, (measurePreserving_eval_infinitePi _ (i, 0)).map_eq]
    exact expMeasure_singleton _ v
  have key := ae_ne_of_indep hXm hYm hind2 hat
  filter_upwards [key] with x hx
  intro heq
  apply hx
  simp only [U, V]
  have e1 : arr x (i, n) = x (i, 0) + ∑ m ∈ Finset.Ico 1 (n + 1), x (i, m) := by
    unfold arr
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have e2 : ∑ m ∈ (range (n' + 1)).attach, x (i', m.1) = arr x (i', n') := by
    unfold arr; exact Finset.sum_attach _ (fun m => x (i', m))
  have e3 : ∑ m ∈ (Finset.Ico 1 (n + 1)).attach, x (i, m.1) = ∑ m ∈ Finset.Ico 1 (n + 1), x (i, m) :=
    Finset.sum_attach _ (fun m => x (i, m))
  rw [e2, e3]
  linarith

/-- almost surely all arrival epochs are distinct. -/
theorem ae_arr_injective (lam : Fin M → ℝ) (hlam : ∀ i, 0 < lam i) :
    ∀ᵐ x ∂(Measure.infinitePi fun j : Fin M × ℕ => expMeasure (lam j.1)),
      Function.Injective (arr x) := by
  have : ∀ j : Fin M × ℕ, IsProbabilityMeasure (expMeasure (lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (hlam j.1)
  have hpos : ∀ᵐ x ∂(Measure.infinitePi fun j : Fin M × ℕ => expMeasure (lam j.1)), ∀ j, 0 < x j := by
    rw [ae_all_iff]; intro j
    exact (measurePreserving_eval_infinitePi _ j).quasiMeasurePreserving.ae (ae_pos_expMeasure _)
  have hne : ∀ᵐ x ∂(Measure.infinitePi fun j : Fin M × ℕ => expMeasure (lam j.1)),
      ∀ j j' : Fin M × ℕ, j.1 ≠ j'.1 → arr x j ≠ arr x j' := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro j'
    by_cases h : j.1 = j'.1
    · exact Filter.Eventually.of_forall fun x hh => absurd h hh
    · filter_upwards [ae_arr_ne lam hlam h j.2 j'.2] with x hx
      exact fun _ => hx
  filter_upwards [hpos, hne] with x hp hn
  intro j j' heq
  by_cases hc : j.1 = j'.1
  · -- same class: strictly increasing in the index
    obtain ⟨i, n⟩ := j
    obtain ⟨i', n'⟩ := j'
    simp only at hc
    subst hc
    have hmono : StrictMono fun n : ℕ => arr x (i, n) := by
      refine strictMono_nat_of_lt_succ fun n => ?_
      unfold arr
      rw [Finset.sum_range_succ _ (n + 1)]
      linarith [hp (i, n + 1)]
    rw [hmono.injective heq]
  · exact absurd heq (hn j j' hc)

end CMA


/-! # 27b64375 P4 (Mathlib only, appended after Det.lean): opener events are measurable mod null.
`{ω | BPS j0 ∧ InB j0 (a j)}` equals, on `DGood`, a countable formula in rationals and arrivals. -/

set_option autoImplicit false

namespace CMQ
open MeasureTheory Set CMX

variable {ι : Type*} {a r : ι → ℝ}

theorem bps_iff_rat (hD : DGood a r) (j0 : ι) :
    BPS a r j0 ↔ ∀ q : ℚ, (q : ℝ) ≤ a j0 → wIn a r q (a j0) ≤ a j0 - q := by
  constructor
  · intro h q hq; exact h q hq
  · intro h s hs
    by_contra hc
    push_neg at hc
    set δ := wIn a r s (a j0) - (a j0 - s) with hδ
    have hδpos : 0 < δ := by linarith
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s - δ < s by linarith)
    have hqs : (q : ℝ) ≤ s := hq2.le
    have hmono : wIn a r s (a j0) ≤ wIn a r q (a j0) := by
      rw [wIn_add a r hD hqs hs]; linarith [wIn_nonneg a r hD q s]
    have := h q (hqs.trans hs)
    linarith

theorem inB_iff_rat (hD : DGood a r) (j0 j : ι) :
    InB a r j0 (a j) ↔ a j0 ≤ a j ∧
      (∀ q : ℚ, a j0 < q → (q : ℝ) ≤ a j → (q : ℝ) - a j0 < wIn a r (a j0) q) ∧
      (∀ j', a j0 < a j' → a j' ≤ a j → a j' - a j0 < wIn a r (a j0) (a j')) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun q hq1 hq2 => h2 q ⟨hq1, hq2⟩, fun j' h1' h2' => h2 _ ⟨h1', h2'⟩⟩
  · rintro ⟨h1, hq, hj⟩
    refine ⟨h1, fun s hs => ?_⟩
    by_contra hc
    push_neg at hc
    classical
    have hFfin : {j' | s ≤ a j' ∧ a j' ≤ a j}.Finite :=
      (hD.fin (a j)).subset (fun j' h => h.2)
    have hjF : j ∈ hFfin.toFinset := hFfin.mem_toFinset.2 ⟨hs.2, le_rfl⟩
    obtain ⟨m, hmF, hmin⟩ := hFfin.toFinset.exists_min_image a ⟨j, hjF⟩
    rw [hFfin.mem_toFinset] at hmF
    rcases eq_or_lt_of_le hmF.1 with heq | hlt
    · have h1m : a j0 < a m := heq ▸ hs.1
      have := hj m h1m hmF.2
      rw [← heq] at this
      linarith
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      have hzero : wIn a r s q = 0 := by
        unfold wIn
        have : ∀ j', Set.indicator {j' : ι | s ≤ a j' ∧ a j' < q} r j' = 0 := by
          intro j'
          refine Set.indicator_of_notMem (fun hh => ?_) _
          have hm' := hmin j' (hFfin.mem_toFinset.2 ⟨hh.1, by linarith [hh.2, hq2, hmF.2]⟩)
          linarith [hh.2]
        simp [this]
      have hadd : wIn a r (a j0) q = wIn a r (a j0) s + wIn a r s q :=
        wIn_add a r hD hs.1.le hq1.le
      have := hq q (hs.1.trans hq1) (hq2.le.trans hmF.2)
      linarith

section meas
variable {Ω : Type*} [MeasurableSpace Ω] [Countable ι]

noncomputable def wInE (A R : Ω → ι → ℝ) (ω : Ω) (s t : ℝ) : ℝ :=
  (∑' j, ENNReal.ofReal (Set.indicator {j | s ≤ A ω j ∧ A ω j < t} (R ω) j)).toReal

lemma wInE_eq (A R : Ω → ι → ℝ) (ω : Ω) (hr : ∀ j, 0 ≤ R ω j) (s t : ℝ) :
    wInE A R ω s t = wIn (A ω) (R ω) s t := by
  unfold wInE wIn
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  congr 1
  funext j
  exact ENNReal.toReal_ofReal (Set.indicator_nonneg (fun j _ => hr j) j)

lemma measurable_wInE {A R : Ω → ι → ℝ} (hA : ∀ j, Measurable fun ω => A ω j)
    (hR : ∀ j, Measurable fun ω => R ω j) {f g : Ω → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun ω => wInE A R ω (f ω) (g ω) := by
  classical
  unfold wInE
  refine (Measurable.ennreal_tsum fun j => ?_).ennreal_toReal
  refine ENNReal.measurable_ofReal.comp ?_
  have hset : MeasurableSet {ω | f ω ≤ A ω j ∧ A ω j < g ω} :=
    (measurableSet_le hf (hA j)).inter (measurableSet_lt (hA j) hg)
  have : (fun ω => Set.indicator {j | f ω ≤ A ω j ∧ A ω j < g ω} (R ω) j) =
      fun ω => if f ω ≤ A ω j ∧ A ω j < g ω then R ω j else 0 := by
    funext ω; simp only [Set.indicator_apply, mem_setOf_eq]
  rw [this]
  exact Measurable.ite hset (hR j) measurable_const

def EvQ (A R : Ω → ι → ℝ) (j0 j : ι) : Set Ω :=
  {ω | (∀ q : ℚ, (q : ℝ) ≤ A ω j0 → wInE A R ω q (A ω j0) ≤ A ω j0 - q) ∧ A ω j0 ≤ A ω j ∧
      (∀ q : ℚ, A ω j0 < q → (q : ℝ) ≤ A ω j → (q : ℝ) - A ω j0 < wInE A R ω (A ω j0) q) ∧
      (∀ j', A ω j0 < A ω j' → A ω j' ≤ A ω j →
        A ω j' - A ω j0 < wInE A R ω (A ω j0) (A ω j'))}

lemma measurableSet_EvQ {A R : Ω → ι → ℝ} (hA : ∀ j, Measurable fun ω => A ω j)
    (hR : ∀ j, Measurable fun ω => R ω j) (j0 j : ι) : MeasurableSet (EvQ A R j0 j) := by
  have hq : ∀ q : ℚ, Measurable fun _ : Ω => (q : ℝ) := fun q => measurable_const
  unfold EvQ
  refine Measurable.setOf ?_
  refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_))
  · refine Measurable.forall fun q => Measurable.imp ?_ ?_
    · exact (measurableSet_le (hq q) (hA j0)).mem
    · exact (measurableSet_le (measurable_wInE hA hR (hq q) (hA j0))
        ((hA j0).sub (hq q))).mem
  · exact (measurableSet_le (hA j0) (hA j)).mem
  · refine Measurable.forall fun q => Measurable.imp ?_ (Measurable.imp ?_ ?_)
    · exact (measurableSet_lt (hA j0) (hq q)).mem
    · exact (measurableSet_le (hq q) (hA j)).mem
    · exact (measurableSet_lt ((hq q).sub (hA j0)) (measurable_wInE hA hR (hA j0) (hq q))).mem
  · refine Measurable.forall fun j' => Measurable.imp ?_ (Measurable.imp ?_ ?_)
    · exact (measurableSet_lt (hA j0) (hA j')).mem
    · exact (measurableSet_le (hA j') (hA j)).mem
    · exact (measurableSet_lt ((hA j').sub (hA j0))
        (measurable_wInE hA hR (hA j0) (hA j'))).mem

theorem EvQ_iff (A R : Ω → ι → ℝ) (ω : Ω) (hD : DGood (A ω) (R ω)) (j0 j : ι) :
    ω ∈ EvQ A R j0 j ↔ BPS (A ω) (R ω) j0 ∧ InB (A ω) (R ω) j0 (A ω j) := by
  have hr : ∀ j, 0 ≤ R ω j := fun j => (hD.rpos j).le
  rw [bps_iff_rat hD, inB_iff_rat hD]
  simp only [EvQ, mem_setOf_eq, wInE_eq A R ω hr]

theorem nullMeasurableSet_opener (μ : Measure Ω) {A R : Ω → ι → ℝ}
    (hA : ∀ j, Measurable fun ω => A ω j) (hR : ∀ j, Measurable fun ω => R ω j)
    (hG : ∀ᵐ ω ∂μ, DGood (A ω) (R ω)) (j0 j : ι) :
    NullMeasurableSet {ω | BPS (A ω) (R ω) j0 ∧ InB (A ω) (R ω) j0 (A ω j)} μ := by
  refine (measurableSet_EvQ hA hR j0 j).nullMeasurableSet.congr ?_
  filter_upwards [hG] with ω hω
  exact propext (EvQ_iff A R ω hω j0 j)

end meas

end CMQ


/-! ## P1b: almost surely, arrival epochs of every class are unbounded (Covers a.s.) -/

namespace CMP
open CoffmanMitrani MeasureTheory ProbabilityTheory Filter Finset

/-- clipping to `[0,1]`. -/
noncomputable def clip (y : ℝ) : ℝ := min (max y 0) 1

lemma measurable_clip : Measurable clip := by
  unfold clip; fun_prop

lemma clip_nonneg (y : ℝ) : 0 ≤ clip y := by
  unfold clip; exact le_min (le_max_right _ _) zero_le_one

lemma clip_le_one (y : ℝ) : clip y ≤ 1 := min_le_right _ _

lemma clip_pos {y : ℝ} (hy : 0 < y) : 0 < clip y := by
  unfold clip; rw [max_eq_left hy.le]; exact lt_min hy one_pos

lemma clip_le {y : ℝ} (hy : 0 ≤ y) : clip y ≤ y := by
  unfold clip; rw [max_eq_left hy]; exact min_le_left _ _

/-- partial sums of iid a.s. positive variables are unbounded a.s. (SLLN on the clipped variables). -/
theorem ae_unbounded {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (hmeas : ∀ n, Measurable (Y n)) (hind : iIndepFun Y μ)
    (hid : ∀ n, IdentDistrib (Y n) (Y 0) μ μ) (hpos : ∀ᵐ ω ∂μ, 0 < Y 0 ω) :
    ∀ᵐ ω ∂μ, ∀ T : ℝ, ∃ n : ℕ, T < ∑ m ∈ range n, clip (Y m ω) := by
  set X : ℕ → Ω → ℝ := fun n ω => clip (Y n ω) with hX
  have hindX : iIndepFun X μ := hind.comp (fun _ => clip) (fun _ => measurable_clip)
  have hidX : ∀ n, IdentDistrib (X n) (X 0) μ μ := fun n => (hid n).comp measurable_clip
  have hmX : Measurable (X 0) := measurable_clip.comp (hmeas 0)
  have hint : Integrable (X 0) μ := by
    refine Integrable.of_bound hmX.aestronglyMeasurable 1 (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (clip_nonneg _)]
    exact clip_le_one _
  have hc : 0 < μ[X 0] := by
    rw [integral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun ω => clip_nonneg _) hint]
    have hs : ∀ᵐ ω ∂μ, ω ∈ Function.support (X 0) := hpos.mono fun ω h => (clip_pos h).ne'
    rw [pos_iff_ne_zero]
    intro h0
    have h1 : μ (Function.support (X 0))ᶜ = 0 := by
      rw [ae_iff] at hs; simpa [Set.compl_def] using hs
    have : μ Set.univ ≤ 0 := by
      calc μ Set.univ = μ (Function.support (X 0) ∪ (Function.support (X 0))ᶜ) := by
            rw [Set.union_compl_self]
        _ ≤ μ (Function.support (X 0)) + μ (Function.support (X 0))ᶜ := measure_union_le _ _
        _ = 0 := by rw [h0, h1, add_zero]
    simp at this
  have hslln := strong_law_ae_real X hint (fun i j hij => hindX.indepFun hij) hidX
  filter_upwards [hslln] with ω hω
  intro T
  set c := μ[X 0]
  have e1 := (tendsto_order.1 hω).1 (c / 2) (half_lt_self hc)
  have e2 : ∀ᶠ n : ℕ in atTop, T * 2 / c < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  have e3 : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  obtain ⟨n, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  refine ⟨n, ?_⟩
  have h4 : c / 2 * n < ∑ i ∈ range n, X i ω := by rwa [lt_div_iff₀ h3] at h1
  have h5 : T < c / 2 * n := by
    have := mul_lt_mul_of_pos_left h2 (half_pos hc)
    have he : c / 2 * (T * 2 / c) = T := by field_simp
    linarith
  exact lt_trans h5 h4

lemma ae_pos_expMeasure (r : ℝ) : ∀ᵐ y ∂(expMeasure r), 0 < y := by
  rw [ae_iff]
  simp only [not_lt]
  unfold expMeasure gammaMeasure
  show (volume.withDensity (gammaPDF 1 r)) (Set.Iic 0) = 0
  rw [withDensity_apply _ measurableSet_Iic, setLIntegral_congr Iio_ae_eq_Iic.symm]
  exact lintegral_gammaPDF_of_nonpos le_rfl

/-- one class's interarrival stream inside the product of exponentials. -/
theorem ae_unbounded_infinitePi {M : ℕ} (rate : Fin M → ℝ) (hrate : ∀ i, 0 < rate i) :
    haveI : ∀ j : Job M, IsProbabilityMeasure (expMeasure (rate j.1)) :=
      fun j => isProbabilityMeasure_expMeasure (hrate j.1)
    ∀ᵐ x ∂(Measure.infinitePi (fun j : Job M => expMeasure (rate j.1))),
      (∀ j, 0 < x j) ∧ ∀ k : Fin M, ∀ T : ℝ, ∃ n : ℕ, T < ∑ m ∈ range n, clip (x (k, m)) := by
  haveI : ∀ j : Job M, IsProbabilityMeasure (expMeasure (rate j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (hrate j.1)
  set μ0 := Measure.infinitePi (fun j : Job M => expMeasure (rate j.1))
  have hpos : ∀ᵐ x ∂μ0, ∀ j, 0 < x j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi _ j).quasiMeasurePreserving.ae (ae_pos_expMeasure _)
  have hall : ∀ᵐ x ∂μ0, ∀ k : Fin M, ∀ T : ℝ, ∃ n : ℕ, T < ∑ m ∈ range n, clip (x (k, m)) := by
    rw [ae_all_iff]
    intro k
    have hind0 : iIndepFun (fun (j : Job M) (x : Job M → ℝ) => x j) μ0 :=
      iIndepFun_infinitePi (X := fun _ y => y) (fun _ => measurable_id)
    have hind : iIndepFun (fun (n : ℕ) (x : Job M → ℝ) => x (k, n)) μ0 :=
      hind0.precomp (g := fun n : ℕ => (k, n)) (fun a b h => by simpa using h)
    refine ae_unbounded (fun n (x : Job M → ℝ) => x (k, n)) (fun n => measurable_pi_apply _)
      hind (fun n => ?_) ?_
    · refine ⟨(measurable_pi_apply _).aemeasurable, (measurable_pi_apply _).aemeasurable, ?_⟩
      rw [(measurePreserving_eval_infinitePi _ (k, n)).map_eq,
        (measurePreserving_eval_infinitePi _ (k, 0)).map_eq]
    · exact (measurePreserving_eval_infinitePi _ (k, 0)).quasiMeasurePreserving.ae
        (ae_pos_expMeasure _)
  filter_upwards [hpos, hall] with x h1 h2
  exact ⟨h1, h2⟩

/-- deterministic step: unbounded clipped partial sums give a finite cover of `{l | arrival ≤ T}`. -/
lemma covers_of {M : ℕ} (x : Job M → ℝ) (hpos : ∀ j, 0 < x j)
    (hu : ∀ k : Fin M, ∀ T : ℝ, ∃ n : ℕ, T < ∑ m ∈ range n, clip (x (k, m))) :
    ∀ T : ℝ, ∃ N0 : ℕ, ∀ l : Job M, (∑ m ∈ range (l.2 + 1), x (l.1, m)) ≤ T → l.2 < N0 := by
  intro T
  choose n hn using fun k => hu k T
  refine ⟨∑ k, n k, fun l hl => ?_⟩
  by_contra hge
  push_neg at hge
  have hk : n l.1 ≤ l.2 :=
    le_trans (Finset.single_le_sum (fun k _ => Nat.zero_le (n k)) (Finset.mem_univ l.1)) hge
  have a1 : ∑ m ∈ range (n l.1), clip (x (l.1, m)) ≤ ∑ m ∈ range (n l.1), x (l.1, m) :=
    Finset.sum_le_sum fun m _ => clip_le (hpos _).le
  have a2 : ∑ m ∈ range (n l.1), x (l.1, m) ≤ ∑ m ∈ range (l.2 + 1), x (l.1, m) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      fun m _ _ => (hpos _).le
  linarith [hn l.1]

/-- P1b on the platform space: a.s. positive interarrivals and every window `(-∞, T]` holds
finitely many arrivals, all of index below some `N0`. -/
theorem ae_covers (D : Data) :
    ∀ᵐ ω ∂D.P, (∀ j, 0 < ω.1 j) ∧
      ∀ T : ℝ, ∃ N0 : ℕ, ∀ l : Job D.M, arrival ω l ≤ T → l.2 < N0 := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  have h1 := ae_unbounded_infinitePi D.lam D.lam_pos
  unfold Data.P
  have g1 := (Measure.quasiMeasurePreserving_fst (μ := Measure.infinitePi
    fun j : Job D.M => expMeasure (D.lam j.1)) (ν := (Measure.infinitePi
      fun j : Job D.M => expMeasure (D.mu j.1)).prod (Measure.infinitePi
        fun _ : Job D.M => Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))).ae h1
  filter_upwards [g1] with ω ⟨hp, hu⟩
  exact ⟨hp, fun T => covers_of ω.1 hp hu T⟩

end CMP


/-! # 27b64375 P1 bridge + IsStrategy for `mix` (needs platform defs, Det, Seed, Arr, Meas, e14b429d_P1). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CMZ
open CoffmanMitrani MeasureTheory ProbabilityTheory Set CMX Filter

section basic
variable {M : ℕ}

lemma arrival_shift (ω : Omega M) : arrival (shift ω) = arrival ω := rfl
lemma serviceReq_shift (ω : Omega M) : serviceReq (shift ω) = serviceReq ω := rfl
lemma classOffset_shift (ω : Omega M) : classOffset (shift ω) = classOffset ω := rfl

lemma measurable_arrival (j : Job M) : Measurable fun ω : Omega M => arrival ω j := by
  unfold arrival
  exact Finset.measurable_sum _ fun m _ => (measurable_pi_apply _).comp measurable_fst

lemma measurable_serviceReq (j : Job M) : Measurable fun ω : Omega M => serviceReq ω j :=
  (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)

structure Good (ω : Omega M) : Prop where
  inc : ∀ j, 0 < ω.1 j
  dg : DGood (arrival ω) (serviceReq ω)
  inj : Function.Injective (arrival ω)

lemma inB_mono {ι : Type*} {a r : ι → ℝ} {j0 : ι} {t u : ℝ} (h : InB a r j0 t)
    (hu1 : a j0 ≤ u) (hu2 : u ≤ t) : InB a r j0 u :=
  ⟨hu1, fun s hs => h.2 s ⟨hs.1, hs.2.trans hu2⟩⟩

lemma le_of_offset {ω : Omega M} (hg : Good ω) (j0 : Job M) (i : Fin M) (m : ℕ)
    (hm : classOffset ω j0 i ≤ m) : arrival ω j0 ≤ arrival ω (i, m) := by
  by_contra hlt
  push_neg at hlt
  have hmono : ∀ m' ≤ m, arrival ω (i, m') ≤ arrival ω (i, m) := fun m' hm' => by
    unfold arrival
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun x _ _ => (hg.inc _).le)
  have hfin : {m' : ℕ | arrival ω (i, m') < arrival ω j0}.Finite := by
    have := hg.dg.fin (arrival ω j0)
    exact (this.preimage (f := fun m' : ℕ => ((i, m') : Job M))
      (fun x _ y _ h => (Prod.ext_iff.1 h).2)).subset
      (fun m' (h : arrival ω (i, m') < arrival ω j0) =>
        show arrival ω (i, m') ≤ arrival ω j0 from le_of_lt h)
  have hsub : (↑(Finset.range (m + 1)) : Set ℕ) ⊆ {m' | arrival ω (i, m') < arrival ω j0} := by
    intro m' hm'
    simp only [Finset.coe_range, Set.mem_Iio] at hm'
    exact lt_of_le_of_lt (hmono m' (by omega)) hlt
  have := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, Finset.card_range] at this
  unfold classOffset at hm
  omega

lemma ae_section {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite ν] {T : Set (α × β)} (hT : NullMeasurableSet T (μ.prod ν)) :
    ∀ᵐ x ∂μ, NullMeasurableSet (Prod.mk x ⁻¹' T) ν := by
  have h := hT.toMeasurable_ae_eq
  have h2 := Measure.ae_ae_of_ae_prod h
  filter_upwards [h2] with x hx
  refine ((measurableSet_toMeasurable (μ.prod ν) T).preimage
    (measurable_prodMk_left : Measurable (Prod.mk x : β → α × β))).nullMeasurableSet.congr ?_
  filter_upwards [hx] with y hy
  exact hy

lemma ae_pos_infinitePi {ι : Type*} [Countable ι] (rate : ι → ℝ) (hrate : ∀ i, 0 < rate i) :
    haveI : ∀ i, IsProbabilityMeasure (expMeasure (rate i)) :=
      fun i => isProbabilityMeasure_expMeasure (hrate i)
    ∀ᵐ x ∂(Measure.infinitePi (fun i => expMeasure (rate i))), ∀ i, 0 < x i := by
  haveI : ∀ i, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hrate i)
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval_infinitePi _ i).quasiMeasurePreserving.ae
    (CMA.ae_pos_expMeasure _)

end basic

theorem ae_good (D : Data) : ∀ᵐ ω ∂D.P, Good ω := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  have hc := CMP.ae_covers D
  have h2 := ae_pos_infinitePi (fun j : Job D.M => D.mu j.1) (fun j => D.mu_pos j.1)
  have hi := CMA.ae_arr_injective D.lam D.lam_pos
  have hr : ∀ᵐ ω ∂D.P, (∀ j, 0 < ω.2.1 j) ∧ Function.Injective (arrival ω) := by
    unfold Data.P
    have g1 := (Measure.quasiMeasurePreserving_fst (μ := Measure.infinitePi
      fun j : Job D.M => expMeasure (D.lam j.1)) (ν := (Measure.infinitePi
        fun j : Job D.M => expMeasure (D.mu j.1)).prod (Measure.infinitePi
          fun _ : Job D.M => Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))).ae hi
    have g2 := (Measure.quasiMeasurePreserving_snd (μ := Measure.infinitePi
      fun j : Job D.M => expMeasure (D.lam j.1)) (ν := (Measure.infinitePi
        fun j : Job D.M => expMeasure (D.mu j.1)).prod (Measure.infinitePi
          fun _ : Job D.M => Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))).ae
      ((Measure.quasiMeasurePreserving_fst).ae h2)
    filter_upwards [g1, g2] with ω h1 h2
    exact ⟨h2, h1⟩
  filter_upwards [hc, hr] with ω h1 h3
  refine ⟨h1.1, ⟨fun j => ?_, h3.1, fun T => ?_⟩, h3.2⟩
  · unfold arrival
    exact Finset.sum_pos (fun m _ => h1.1 _) ⟨0, by simp⟩
  · obtain ⟨N0, hN⟩ := h1.2 T
    exact ((Set.finite_univ (α := Fin D.M)).prod (Set.finite_lt_nat N0)).subset
      (fun l hl => ⟨trivial, hN l hl⟩)

theorem mp_shift (D : Data) : MeasurePreserving (shift (M := D.M)) D.P D.P := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  have h := (MeasurePreserving.id (Measure.infinitePi fun j : Job D.M => expMeasure (D.lam j.1))).prod
    ((MeasurePreserving.id (Measure.infinitePi fun j : Job D.M => expMeasure (D.mu j.1))).prod
      (CMY.mp_sig (ι := Job D.M) (volume : Measure unitInterval)))
  unfold Data.P
  exact h

section mixing
variable {D : Data} {K : ℕ} (α : Fin (K + 1) → ℝ)

lemma measurable_mixType : Measurable (mixType α) := by
  classical
  let c : Fin (K + 1) → ℝ := fun j => ∑ l ∈ Finset.Iic j, α l
  let G : unitInterval → (Fin (K + 1) → Bool) := fun u j => decide ((u : ℝ) < c j)
  let F : (Fin (K + 1) → Bool) → Fin (K + 1) := fun b =>
    if h : ∃ j, b j = true then
      (Finset.univ.filter (fun j => b j = true)).min'
        (let ⟨j, hj⟩ := h; ⟨j, by simp [hj]⟩)
    else Fin.last K
  have hFG : mixType α = F ∘ G := by
    funext u
    simp only [mixType, F, G, c, Function.comp, decide_eq_true_eq]
  rw [hFG]
  refine (measurable_of_countable F).comp ?_
  refine measurable_pi_lambda _ fun j => ?_
  refine measurable_to_bool ?_
  have : (fun u => G u j) ⁻¹' {true} = {u : unitInterval | (u : ℝ) < c j} := by
    ext u; simp [G]
  rw [this]
  exact measurableSet_lt measurable_subtype_coe measurable_const

variable {S : Fin (K + 1) → Schedule D.M}

structure GoodM (S : Fin (K + 1) → Schedule D.M)
    (rule : Fin (K + 1) → History D.M → (ℕ → unitInterval) → Option (Fin D.M × ℕ))
    (ω : Omega D.M) : Prop where
  g : Good ω
  sk : ∀ k, SGood (arrival ω) (serviceReq ω) (S k (shift ω))
  done : ∀ k j, ∃ t, serviceReq ω j ≤ served (S k) j (shift ω) t
  rl : ∀ k (j0 : Job D.M) (t : ℝ), IsBPStart ω j0 → InBP ω j0 t →
    S k (shift ω) t = (rule k (history (S k) (shift ω) j0 t) (fun l => seed ω j0 (l + 1))).map
      (fun p => (p.1, classOffset ω j0 p.1 + p.2))

theorem ae_goodM (S : Fin (K + 1) → Schedule D.M) (hS : ∀ k, IsStrategy D (S k)) :
    ∃ rule, ∀ᵐ ω ∂D.P, GoodM S rule ω := by
  have hS2 := fun k => (hS k).2
  choose rule hrule using hS2
  refine ⟨rule, ?_⟩
  have hmp := mp_shift D
  have hQ := hmp.quasiMeasurePreserving.ae (ae_all_iff.2 hrule)
  have hsec : ∀ᵐ ω ∂D.P, ∀ k j, NullMeasurableSet {s : ℝ | S k ω s = some j} volume :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun j => ae_section ((hS k).1 j)
  have hsec' := hmp.quasiMeasurePreserving.ae hsec
  filter_upwards [ae_good D, hQ, hsec'] with ω hg hq hs
  exact ⟨hg, fun k => ⟨fun t j h => (hq k).1 t j h, fun t => (hq k).2.1 t, fun j => hs k j⟩,
    fun k j => (hq k).2.2.1 j, fun k j0 t hB hI => (hq k).2.2.2 j0 t hB hI⟩

variable {rule : Fin (K + 1) → History D.M → (ℕ → unitInterval) → Option (Fin D.M × ℕ)}
  {ω : Omega D.M}

lemma mixSpec (h : GoodM S rule ω) :
    MixSpec (arrival ω) (serviceReq ω) (fun k => S k (shift ω))
      (fun j0 => mixType α (seed ω j0 0)) (mix α S ω) where
  on t j0 hB hI := by
    have hex : ∃ j0, IsBPStart ω j0 ∧ InBP ω j0 t := ⟨j0, hB, hI⟩
    have hc : hex.choose = j0 := h.g.inj
      (eq_of_two (a := arrival ω) (r := serviceReq ω) hex.choose_spec.1 hB hex.choose_spec.2 hI)
    show mix α S ω t = S (mixType α (seed ω j0 0)) (shift ω) t
    simp only [mix, dif_pos hex]
    rw [hc]
  off t hoff := by
    show mix α S ω t = none
    simp only [mix]
    rw [dif_neg]
    rintro ⟨j0, hB, hI⟩
    exact hoff j0 hB hI

lemma mix_sgood (h : GoodM S rule ω) : SGood (arrival ω) (serviceReq ω) (mix α S ω) :=
  mix_good h.g.dg h.g.inj h.sk (mixSpec α h)

lemma history_mix (h : GoodM S rule ω) {j0 : Job D.M} {t : ℝ} (hB : IsBPStart ω j0)
    (hI : InBP ω j0 t) :
    history (mix α S) ω j0 t = history (S (mixType α (seed ω j0 0))) (shift ω) j0 t := by
  have hM := mixSpec α h
  have hSG := mix_sgood α h
  have hI' : InB (arrival ω) (serviceReq ω) j0 t := hI
  unfold history
  congr 1
  · funext s
    show (if 0 ≤ s ∧ s < t - arrival ω j0 then
        (mix α S ω (arrival ω j0 + s)).map (fun j => (j.1, j.2 - classOffset ω j0 j.1))
        else none) =
      (if 0 ≤ s ∧ s < t - arrival ω j0 then
        (S (mixType α (seed ω j0 0)) (shift ω) (arrival ω j0 + s)).map
          (fun j => (j.1, j.2 - classOffset ω j0 j.1))
        else none)
    split_ifs with hs
    · rw [hM.on _ j0 hB (inB_mono hI' (by linarith [hs.1]) (by linarith [hs.2]))]
    · rfl
  · funext p
    show (if serviceReq ω (p.1, classOffset ω j0 p.1 + p.2) ≤
          served (mix α S) (p.1, classOffset ω j0 p.1 + p.2) ω t then
        some (departure (mix α S) (p.1, classOffset ω j0 p.1 + p.2) ω - arrival ω j0)
        else none) =
      (if serviceReq ω (p.1, classOffset ω j0 p.1 + p.2) ≤
          served (S (mixType α (seed ω j0 0))) (p.1, classOffset ω j0 p.1 + p.2) (shift ω) t then
        some (departure (S (mixType α (seed ω j0 0))) (p.1, classOffset ω j0 p.1 + p.2) (shift ω)
          - arrival ω j0)
        else none)
    have hle : arrival ω j0 ≤ arrival ω (p.1, classOffset ω j0 p.1 + p.2) :=
      le_of_offset h.g j0 p.1 _ (Nat.le_add_right _ _)
    by_cases hj : arrival ω (p.1, classOffset ω j0 p.1 + p.2) ≤ t
    · have hIj := inB_mono hI' hle hj
      have hsrv := mix_srv h.g.dg h.g.inj h.sk hM hB hIj
      have e1 : served (mix α S) (p.1, classOffset ω j0 p.1 + p.2) ω =
          served (S (mixType α (seed ω j0 0))) (p.1, classOffset ω j0 p.1 + p.2) (shift ω) := hsrv
      unfold departure
      rw [e1]
      rfl
    · have hlt : t ≤ arrival ω (p.1, classOffset ω j0 p.1 + p.2) := (not_le.1 hj).le
      have h0 : served (mix α S) (p.1, classOffset ω j0 p.1 + p.2) ω t = 0 :=
        srv_eq_zero (mix α S ω) _ (arrival ω) (fun u hu => (hSG.feas u _ hu).1) hlt
      have h0' : served (S (mixType α (seed ω j0 0))) (p.1, classOffset ω j0 p.1 + p.2)
          (shift ω) t = 0 :=
        srv_eq_zero _ _ (arrival ω) (fun u hu => ((h.sk _).feas u _ hu).1) hlt
      rw [if_neg (by rw [h0]; exact not_le.2 (h.g.dg.rpos _)),
        if_neg (by rw [h0']; exact not_le.2 (h.g.dg.rpos _))]

lemma mix_iff (h : GoodM S rule ω) (t : ℝ) (j : Job D.M) :
    mix α S ω t = some j ↔ ∃ j0, (IsBPStart ω j0 ∧ InBP ω j0 (arrival ω j)) ∧
      ∃ k, mixType α (ω.2.2 j0 0) = k ∧ S k (shift ω) t = some j := by
  constructor
  · intro ht
    obtain ⟨j0, hB, hj⟩ := exists_opener h.g.dg j
    refine ⟨j0, ⟨hB, hj⟩, _, rfl, ?_⟩
    have := mix_set h.g.dg h.g.inj h.sk (mixSpec α h) hB hj
    exact (Set.ext_iff.1 this t).1 ht
  · rintro ⟨j0, ⟨hB, hj⟩, k, rfl, ht⟩
    have := mix_set h.g.dg h.g.inj h.sk (mixSpec α h) hB hj
    exact (Set.ext_iff.1 this t).2 ht

lemma isProb_P (D : Data) : IsProbabilityMeasure D.P := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  unfold Data.P
  infer_instance

theorem mix_meas (hS : ∀ k, IsStrategy D (S k)) (hG : ∀ᵐ ω ∂D.P, GoodM S rule ω)
    (j : Job D.M) :
    NullMeasurableSet {p : Omega D.M × ℝ | mix α S p.1 p.2 = some j} (D.P.prod volume) := by
  haveI := isProb_P D
  have hU : NullMeasurableSet (⋃ j0 : Job D.M, ⋃ k : Fin (K + 1),
      (({ω : Omega D.M | IsBPStart ω j0 ∧ InBP ω j0 (arrival ω j)} ∩
        {ω | mixType α (ω.2.2 j0 0) = k}) ×ˢ (univ : Set ℝ)) ∩
      (Prod.map shift id) ⁻¹' {p : Omega D.M × ℝ | S k p.1 p.2 = some j}) (D.P.prod volume) := by
    refine NullMeasurableSet.iUnion fun j0 => NullMeasurableSet.iUnion fun k => ?_
    refine NullMeasurableSet.inter (NullMeasurableSet.prod (NullMeasurableSet.inter ?_ ?_)
      nullMeasurableSet_univ) ?_
    · exact CMQ.nullMeasurableSet_opener D.P (A := fun ω => arrival ω)
        (R := fun ω => serviceReq ω) measurable_arrival measurable_serviceReq
        (hG.mono fun ω h => h.g.dg) j0 j
    · exact (((measurable_mixType α).comp ((measurable_pi_apply 0).comp
        ((measurable_pi_apply j0).comp (measurable_snd.comp measurable_snd))))
          (measurableSet_singleton k)).nullMeasurableSet
    · exact ((hS k).1 j).preimage
        ((mp_shift D).prod (MeasurePreserving.id (volume : Measure ℝ))).quasiMeasurePreserving
  refine hU.congr ?_
  have hG' : ∀ᵐ p ∂(D.P.prod volume), GoodM S rule p.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := D.P) (ν := (volume : Measure ℝ))).ae hG
  filter_upwards [hG'] with p hp
  apply propext
  change p ∈ (⋃ j0 : Job D.M, ⋃ k : Fin (K + 1),
      (({ω : Omega D.M | IsBPStart ω j0 ∧ InBP ω j0 (arrival ω j)} ∩
        {ω | mixType α (ω.2.2 j0 0) = k}) ×ˢ (univ : Set ℝ)) ∩
      (Prod.map shift id) ⁻¹' {p : Omega D.M × ℝ | S k p.1 p.2 = some j}) ↔
    mix α S p.1 p.2 = some j
  rw [mix_iff α hp]
  simp only [mem_iUnion, mem_inter_iff, mem_prod, mem_setOf_eq, mem_univ, and_true,
    mem_preimage, Prod.map, id]
  constructor
  · rintro ⟨j0, k, ⟨hE, hk⟩, hS'⟩
    exact ⟨j0, hE, k, hk, hS'⟩
  · rintro ⟨j0, hE, k, hk, hS'⟩
    exact ⟨j0, k, ⟨hE, hk⟩, hS'⟩

theorem isStrategy_mix (hS : ∀ k, IsStrategy D (S k)) : IsStrategy D (mix α S) := by
  obtain ⟨rule, hG⟩ := ae_goodM S hS
  refine ⟨mix_meas α hS hG, fun hist u => rule (mixType α (u 0)) hist (fun l => u (l + 1)), ?_⟩
  filter_upwards [hG] with ω h
  have hM := mixSpec α h
  have hSG := mix_sgood α h
  refine ⟨fun t j ht => hSG.feas t j ht, fun t => hSG.idle t, fun j => ?_,
    fun j0 t hB hI => ?_⟩
  · obtain ⟨j0, hB, hj⟩ := exists_opener h.g.dg j
    obtain ⟨t, ht⟩ := h.done (mixType α (seed ω j0 0)) j
    refine ⟨t, ?_⟩
    have hs := mix_srv h.g.dg h.g.inj h.sk hM hB hj
    show serviceReq ω j ≤ srv (mix α S ω) j t
    rw [hs]
    exact ht
  · rw [hM.on t j0 hB hI]
    show S (mixType α (seed ω j0 0)) (shift ω) t =
      (rule (mixType α (seed ω j0 0)) (history (mix α S) ω j0 t)
        (fun l => seed ω j0 (l + 1))).map (fun p => (p.1, classOffset ω j0 p.1 + p.2))
    rw [history_mix α h hB hI]
    exact h.rl _ j0 t hB hI

end mixing

end CMZ


/-! # 27b64375 Achieves for `mix` (after Main1). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CMW
open MeasureTheory ProbabilityTheory Set CMY Filter

variable {ι : Type*} [Countable ι] {E : Type*} [MeasurableSpace E] (η : Measure E)
  [IsProbabilityMeasure η] {X : Type*} [MeasurableSpace X] (ρ : Measure X) [SFinite ρ]

theorem integral_mixfac (Jf : X → ι) {g : E → ℝ} (hg : Measurable g) (hgb : ∀ u, |g u| ≤ 1)
    {H : X × (ι → ℕ → E) → ℝ} (hH : Integrable H (ρ.prod (C η)))
    (hF : AEStronglyMeasurable (fun p : X × (ι → ℕ → E) => g (p.2 (Jf p.1) 0) * H (p.1, sig p.2))
      (ρ.prod (C η))) :
    ∫ p, g (p.2 (Jf p.1) 0) * H (p.1, sig p.2) ∂(ρ.prod (C η)) =
      (∫ u, g u ∂η) * ∫ p, H p ∂(ρ.prod (C η)) := by
  have hmp : MeasurePreserving (Prod.map id sig : X × (ι → ℕ → E) → X × (ι → ℕ → E))
      (ρ.prod (C η)) (ρ.prod (C η)) :=
    (MeasurePreserving.id ρ).prod (mp_sig η)
  have hH' : Integrable (fun p : X × (ι → ℕ → E) => H (p.1, sig p.2)) (ρ.prod (C η)) :=
    hmp.integrable_comp_of_integrable hH
  have hFi : Integrable (fun p : X × (ι → ℕ → E) => g (p.2 (Jf p.1) 0) * H (p.1, sig p.2))
      (ρ.prod (C η)) := by
    refine hH'.mono hF (Eventually.of_forall fun p => ?_)
    rw [norm_mul, Real.norm_eq_abs (g _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hgb _)
  rw [integral_prod _ hFi, integral_prod _ hH, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hH.prod_right_ae] with x hx
  exact integral_hd_mul_sig η (Jf x) hg hx.aestronglyMeasurable

end CMW

namespace CMZ
open CoffmanMitrani MeasureTheory ProbabilityTheory Set CMX Filter

section ach
variable {D : Data} {K : ℕ} (α : Fin (K + 1) → ℝ)

lemma mixType_eq_iff (hα : ∀ j, 0 ≤ α j) (hα1 : ∑ j, α j = 1) (u : unitInterval)
    (hu : (u : ℝ) < 1) (k : Fin (K + 1)) :
    mixType α u = k ↔ (∑ l ∈ Finset.Iio k, α l) ≤ u ∧ (u : ℝ) < ∑ l ∈ Finset.Iic k, α l := by
  classical
  have hlast : ∑ l ∈ Finset.Iic (Fin.last K), α l = 1 := by
    rw [← hα1]; congr 1; ext l; simp [Fin.le_last]
  have hex : ∃ j : Fin (K + 1), (u : ℝ) < ∑ l ∈ Finset.Iic j, α l :=
    ⟨Fin.last K, by rw [hlast]; exact hu⟩
  have hF : ∀ j, j ∈ Finset.univ.filter (fun j : Fin (K + 1) => (u : ℝ) < ∑ l ∈ Finset.Iic j, α l)
      ↔ (u : ℝ) < ∑ l ∈ Finset.Iic j, α l := fun j => by simp
  unfold mixType
  rw [dif_pos hex]
  generalize_proofs H
  constructor
  · intro hk
    have hkF := Finset.min'_mem _ H
    rw [hk, hF] at hkF
    refine ⟨?_, hkF⟩
    by_cases h0 : k.val = 0
    · have : Finset.Iio k = ∅ := by
        ext l; simp [Fin.lt_iff_val_lt_val, h0]
      rw [this, Finset.sum_empty]; exact u.2.1
    · have hIj : Finset.Iic (⟨k.val - 1, by omega⟩ : Fin (K + 1)) = Finset.Iio k := by
        ext l; simp only [Finset.mem_Iic, Finset.mem_Iio, Fin.le_def, Fin.lt_def]; omega
      rw [← hIj]
      by_contra hc
      push_neg at hc
      have hjF := (hF _).2 hc
      have := Finset.min'_le _ _ hjF
      rw [hk, Fin.le_iff_val_le_val] at this
      simp only at this
      omega
  · rintro ⟨h1, h2⟩
    have hkF := (hF k).2 h2
    refine le_antisymm (Finset.min'_le _ k hkF) ?_
    by_contra hc
    push_neg at hc
    have hm := Finset.min'_mem _ H
    rw [hF] at hm
    have : ∑ l ∈ Finset.Iic (Finset.min' _ H), α l ≤ ∑ l ∈ Finset.Iio k, α l :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun l hl => by simp only [Finset.mem_Iic, Finset.mem_Iio] at hl ⊢; exact lt_of_le_of_lt hl hc)
        (fun l _ _ => hα l)
    linarith

lemma vol_mixType (hα : ∀ j, 0 ≤ α j) (hα1 : ∑ j, α j = 1) (k : Fin (K + 1)) :
    (volume {u : unitInterval | mixType α u = k}).toReal = α k := by
  classical
  set cp := ∑ l ∈ Finset.Iio k, α l with hcp
  set c := ∑ l ∈ Finset.Iic k, α l with hc
  have hck : c = cp + α k := by
    rw [hc, hcp, ← Finset.Iio_insert, Finset.sum_insert (by simp), add_comm]
  have hcp0 : 0 ≤ cp := Finset.sum_nonneg fun l _ => hα l
  have hc1 : c ≤ 1 := by
    rw [← hα1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun l _ _ => hα l)
  set x : unitInterval := ⟨cp, hcp0, by linarith [hα k]⟩
  set y : unitInterval := ⟨c, by linarith [hα k], hc1⟩
  have h1 : Ico x y ⊆ {u : unitInterval | mixType α u = k} := by
    intro u hu
    have hu1 : (u : ℝ) < 1 := lt_of_lt_of_le (show (u : ℝ) < c from hu.2) hc1
    exact (mixType_eq_iff α hα hα1 u hu1 k).2 ⟨hu.1, hu.2⟩
  have h2 : {u : unitInterval | mixType α u = k} ⊆ Ico x y ∪ {1} := by
    intro u hu
    by_cases hu1 : (u : ℝ) < 1
    · exact Or.inl ((mixType_eq_iff α hα hα1 u hu1 k).1 hu)
    · right
      exact Subtype.ext (le_antisymm u.2.2 (not_lt.1 hu1))
  have hle1 := measure_mono (μ := (volume : Measure unitInterval)) h1
  have hle2 := (measure_mono (μ := (volume : Measure unitInterval)) h2).trans
    (measure_union_le _ _)
  rw [measure_singleton, add_zero] at hle2
  have heq := le_antisymm hle2 hle1
  rw [heq, unitInterval.volume_Ico, ENNReal.toReal_ofReal]
  · show c - cp = α k
    linarith
  · show 0 ≤ c - cp
    linarith [hα k]

variable {S : Fin (K + 1) → Schedule D.M}

open Classical in
noncomputable def opener (j : Job D.M) (ω : Omega D.M) : Job D.M :=
  if h : ∃ j0, IsBPStart ω j0 ∧ InBP ω j0 (arrival ω j) then h.choose else j

variable {rule : Fin (K + 1) → History D.M → (ℕ → unitInterval) → Option (Fin D.M × ℕ)}

lemma opener_spec {ω : Omega D.M} (h : GoodM S rule ω) (j : Job D.M) :
    IsBPStart ω (opener j ω) ∧ InBP ω (opener j ω) (arrival ω j) := by
  have hex : ∃ j0, IsBPStart ω j0 ∧ InBP ω j0 (arrival ω j) := exists_opener h.g.dg j
  unfold opener
  rw [dif_pos hex]
  exact hex.choose_spec

lemma resp_mix {ω : Omega D.M} (h : GoodM S rule ω) (j : Job D.M) :
    responseTime (mix α S) j ω =
      responseTime (S (mixType α (ω.2.2 (opener j ω) 0))) j (shift ω) := by
  obtain ⟨hB, hj⟩ := opener_spec h j
  have hs := mix_srv h.g.dg h.g.inj h.sk (mixSpec α h) hB hj
  have e1 : served (mix α S) j ω = served (S (mixType α (ω.2.2 (opener j ω) 0))) j (shift ω) := hs
  unfold responseTime departure
  rw [e1]
  rfl

lemma nm_T (hG : ∀ᵐ ω ∂D.P, GoodM S rule ω) (j : Job D.M) (k : Fin (K + 1)) :
    NullMeasurableSet {ω : Omega D.M | mixType α (ω.2.2 (opener j ω) 0) = k} D.P := by
  have hU : NullMeasurableSet (⋃ j0 : Job D.M,
      {ω : Omega D.M | IsBPStart ω j0 ∧ InBP ω j0 (arrival ω j)} ∩
        {ω | mixType α (ω.2.2 j0 0) = k}) D.P := by
    refine NullMeasurableSet.iUnion fun j0 => NullMeasurableSet.inter ?_ ?_
    · exact CMQ.nullMeasurableSet_opener D.P (A := fun ω => arrival ω)
        (R := fun ω => serviceReq ω) measurable_arrival measurable_serviceReq
        (hG.mono fun ω h => h.g.dg) j0 j
    · exact (((measurable_mixType α).comp ((measurable_pi_apply 0).comp
        ((measurable_pi_apply j0).comp (measurable_snd.comp measurable_snd))))
          (measurableSet_singleton k)).nullMeasurableSet
  refine hU.congr ?_
  filter_upwards [hG] with ω h
  apply propext
  change ω ∈ (⋃ j0 : Job D.M,
      {ω : Omega D.M | IsBPStart ω j0 ∧ InBP ω j0 (arrival ω j)} ∩
        {ω | mixType α (ω.2.2 j0 0) = k}) ↔ mixType α (ω.2.2 (opener j ω) 0) = k
  simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨j0, ⟨hB, hj⟩, hk⟩
    have hsp := opener_spec h j
    have : opener j ω = j0 := h.g.inj
      (eq_of_two (a := arrival ω) (r := serviceReq ω) hsp.1 hB hsp.2 hj)
    rw [this]
    exact hk
  · intro hk
    exact ⟨opener j ω, opener_spec h j, hk⟩

/-- the `k`-th piece of the mixed response time. -/
noncomputable def piece (S : Fin (K + 1) → Schedule D.M) (j : Job D.M) (k : Fin (K + 1))
    (ω : Omega D.M) : ℝ :=
  Set.indicator {ω : Omega D.M | mixType α (ω.2.2 (opener j ω) 0) = k}
    (fun ω => responseTime (S k) j (shift ω)) ω

lemma opener_indep (j : Job D.M) (x y : Job D.M → ℝ) (c c' : Job D.M → ℕ → unitInterval) :
    opener j (x, (y, c)) = opener j (x, (y, c')) := rfl

theorem integral_piece (hα : ∀ j, 0 ≤ α j) (hα1 : ∑ j, α j = 1)
    (hG : ∀ᵐ ω ∂D.P, GoodM S rule ω) (j : Job D.M) (k : Fin (K + 1))
    (hRk : Integrable (fun ω => responseTime (S k) j ω) D.P) :
    ∫ ω, piece α S j k ω ∂D.P = α k * ∫ ω, responseTime (S k) j ω ∂D.P := by
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  haveI := isProb_P D
  have hpm : AEStronglyMeasurable (piece α S j k) D.P :=
    (hRk.aestronglyMeasurable.comp_measurePreserving (mp_shift D)).indicator₀ (nm_T α hG j k)
  have hRk' := hRk
  unfold Data.P at hpm hRk' ⊢
  set A := Measure.infinitePi fun j : Job D.M => expMeasure (D.lam j.1)
  set B := Measure.infinitePi fun j : Job D.M => expMeasure (D.mu j.1)
  have hmpA := measurePreserving_prodAssoc A B (CMY.C (ι := Job D.M) (volume : Measure unitInterval))
  set g : unitInterval → ℝ := Set.indicator {u : unitInterval | mixType α u = k} (fun _ => (1 : ℝ))
  have hg : Measurable g := measurable_const.indicator (measurable_mixType α (measurableSet_singleton k))
  have hgb : ∀ u, |g u| ≤ 1 := fun u => by
    simp only [g, Set.indicator_apply]; split_ifs <;> norm_num
  have hgi : ∫ u, g u ∂(volume : Measure unitInterval) = α k := by
    show ∫ u, Set.indicator {u : unitInterval | mixType α u = k} 1 u ∂volume = α k
    rw [integral_indicator_one (s := {u : unitInterval | mixType α u = k})
      (measurable_mixType α (measurableSet_singleton k)), Measure.real]
    exact vol_mixType α hα hα1 k
  set Jf : (Job D.M → ℝ) × (Job D.M → ℝ) → Job D.M := fun xy => opener j (xy.1, (xy.2, fun _ _ => 0))
  set H : ((Job D.M → ℝ) × (Job D.M → ℝ)) × (Job D.M → ℕ → unitInterval) → ℝ :=
    fun p => responseTime (S k) j (MeasurableEquiv.prodAssoc p)
  have hH : Integrable H ((A.prod B).prod (CMY.C (volume : Measure unitInterval))) :=
    (hmpA.integrable_comp_emb (MeasurableEquiv.prodAssoc).measurableEmbedding).2 hRk'
  have hpt : ∀ p : ((Job D.M → ℝ) × (Job D.M → ℝ)) × (Job D.M → ℕ → unitInterval),
      piece α S j k (MeasurableEquiv.prodAssoc p) = g (p.2 (Jf p.1) 0) * H (p.1, CMY.sig p.2) := by
    rintro ⟨⟨x, y⟩, c⟩
    show Set.indicator {ω : Omega D.M | mixType α (ω.2.2 (opener j ω) 0) = k}
        (fun ω => responseTime (S k) j (shift ω)) (x, (y, c)) =
      Set.indicator {u : unitInterval | mixType α u = k} (fun _ => (1 : ℝ)) (c (Jf (x, y)) 0) *
        responseTime (S k) j (x, (y, CMY.sig c))
    by_cases hk : mixType α (c (Jf (x, y)) 0) = k
    · rw [Set.indicator_of_mem (show (x, (y, c)) ∈
          {ω : Omega D.M | mixType α (ω.2.2 (opener j ω) 0) = k} from hk),
        Set.indicator_of_mem (show c (Jf (x, y)) 0 ∈ {u : unitInterval | mixType α u = k} from hk),
        one_mul]
      rfl
    · rw [Set.indicator_of_notMem (show (x, (y, c)) ∉
          {ω : Omega D.M | mixType α (ω.2.2 (opener j ω) 0) = k} from hk),
        Set.indicator_of_notMem (show c (Jf (x, y)) 0 ∉ {u : unitInterval | mixType α u = k} from hk),
        zero_mul]
  have hF : AEStronglyMeasurable (fun p : ((Job D.M → ℝ) × (Job D.M → ℝ)) ×
      (Job D.M → ℕ → unitInterval) => g (p.2 (Jf p.1) 0) * H (p.1, CMY.sig p.2))
      ((A.prod B).prod (CMY.C (volume : Measure unitInterval))) := by
    have := hpm.comp_measurePreserving hmpA
    refine this.congr (Eventually.of_forall fun p => ?_)
    exact hpt p
  change ∫ ω, piece α S j k ω ∂(A.prod (B.prod (CMY.C (ι := Job D.M) (volume : Measure unitInterval))))
    = α k * ∫ ω, responseTime (S k) j ω ∂(A.prod (B.prod
      (CMY.C (ι := Job D.M) (volume : Measure unitInterval))))
  rw [← hmpA.integral_comp', ← hmpA.integral_comp']
  simp only [hpt]
  rw [CMW.integral_mixfac (volume : Measure unitInterval) (A.prod B) Jf hg hgb hH hF, hgi]

theorem achieves_mix (S : Fin (K + 1) → Schedule D.M) (Wv : Fin (K + 1) → Fin D.M → ℝ)
    (hS : ∀ k, IsStrategy D (S k)) (hW : ∀ k, Achieves D (S k) (Wv k))
    (hα : ∀ j, 0 ≤ α j) (hα1 : ∑ j, α j = 1) :
    Achieves D (mix α S) (∑ k, α k • Wv k) := by
  obtain ⟨rule, hG⟩ := ae_goodM S hS
  intro i
  have hdec : ∀ n, (fun ω => responseTime (mix α S) (i, n) ω) =ᵐ[D.P]
      fun ω => ∑ k, piece α S (i, n) k ω := by
    intro n
    filter_upwards [hG] with ω h
    rw [resp_mix α h, Finset.sum_eq_single (mixType α (ω.2.2 (opener (i, n) ω) 0))]
    · simp [piece, Set.indicator_apply]
    · intro b _ hb
      simp only [piece, Set.indicator_apply, mem_setOf_eq]
      rw [if_neg (Ne.symm hb)]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  have hint : ∀ n k, Integrable (piece α S (i, n) k) D.P := fun n k =>
    ((mp_shift D).integrable_comp_of_integrable ((hW k i).1 n)).indicator₀ (nm_T α hG (i, n) k)
  refine ⟨fun n => ?_, ?_⟩
  · exact (integrable_finset_sum _ fun k _ => hint n k).congr (hdec n).symm
  · have key : ∀ n, ∫ ω, responseTime (mix α S) (i, n) ω ∂D.P =
        ∑ k, α k * ∫ ω, responseTime (S k) (i, n) ω ∂D.P := by
      intro n
      rw [integral_congr_ae (hdec n), integral_finset_sum _ fun k _ => hint n k]
      exact Finset.sum_congr rfl fun k _ => integral_piece α hα hα1 hG (i, n) k ((hW k i).1 n)
    simp only [key, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact tendsto_finset_sum _ fun k _ => ((hW k i).2).const_mul (α k)

end ach

end CMZ

open CoffmanMitrani in
theorem solution (D : Data) {K : ℕ} (S : Fin (K + 1) → Schedule D.M)
    (Wv : Fin (K + 1) → Fin D.M → ℝ) (α : Fin (K + 1) → ℝ)
    (hS : ∀ j, IsStrategy D (S j)) (hW : ∀ j, Achieves D (S j) (Wv j))
    (hα : ∀ j, 0 ≤ α j) (hα1 : ∑ j, α j = 1) :
    IsStrategy D (mix α S) ∧ Achieves D (mix α S) (∑ j, α j • Wv j) := by
  exact ⟨CMZ.isStrategy_mix α hS, CMZ.achieves_mix α S Wv hS hW hα hα1⟩

