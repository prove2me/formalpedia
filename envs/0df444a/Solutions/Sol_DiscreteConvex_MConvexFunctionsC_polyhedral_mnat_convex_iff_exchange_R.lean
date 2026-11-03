-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsC.polyhedral_mnat_convex_iff_exchange_R
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T06:33:27.574297+00:00
-- url     : https://prove2.me/submissions/7522d99f-f765-4fc7-8520-492409107cae

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvexR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatExchangeAxiomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_IsPolyhedralConvex

open scoped Pointwise BigOperators
open Classical
open DiscreteConvex.MConvexFunctionsC

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PolyMNatEquiv

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma coe_untopD {x : WithTop ℝ} (hx : x ≠ ⊤) : ((x.untopD 0 : ℝ) : WithTop ℝ) = x := by
  cases x with
  | top => exact absurd rfl hx
  | coe r => rfl

lemma ne_top_of_add_le {a b c d : WithTop ℝ} (h : a + b ≤ c + d)
    (hc : c ≠ ⊤) (hd : d ≠ ⊤) : a ≠ ⊤ ∧ b ≠ ⊤ := by
  have hcd : c + d ≠ ⊤ := WithTop.add_ne_top.mpr ⟨hc, hd⟩
  exact WithTop.add_ne_top.mp (ne_top_of_le_ne_top hcd h)

lemma finite_pos_bound {I : Type*} [DecidableEq I] (s : Finset I)
    (f : I → ℝ) (hf : ∀ i ∈ s, 0 < f i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i ∈ s, e ≤ f i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert i s _ ih =>
    obtain ⟨e, he, hbound⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min e (f i), lt_min he (hf i (Finset.mem_insert_self _ _)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hbound j hj)

def epiPoint (p : V → ℝ) (r : ℝ) : Option V → ℝ
  | none => r
  | some v => p v

@[simp] lemma row_epi (a : Option V → ℝ) (p : V → ℝ) (r : ℝ) :
    (∑ w : Option V, a w * epiPoint p r w) = a none * r + ∑ v : V, a (some v) * p v := by
  simp [Fintype.sum_option, epiPoint]

section PolyTangent

variable {m : ℕ} (g : (V → ℝ) → WithTop ℝ) (a : Fin m → Option V → ℝ) (b : Fin m → ℝ)

def HasPolyRep : Prop :=
  ∀ (q : V → ℝ) (s : ℝ),
    g q ≤ (s : WithTop ℝ) ↔ ∀ i : Fin m, a i none * s + ∑ v : V, a i (some v) * q v ≤ b i

lemma exists_poly_rep (hpoly : IsPolyhedralConvex g) :
    ∃ (m : ℕ) (a : Fin m → Option V → ℝ) (b : Fin m → ℝ), HasPolyRep g a b := by
  obtain ⟨m, a, b, hab⟩ := hpoly
  refine ⟨m, a, b, fun q s => ?_⟩
  have h := Set.ext_iff.mp hab (epiPoint q s)
  change g q ≤ (s : WithTop ℝ) ↔ (∀ i, ∑ w, a i w * epiPoint q s w ≤ b i) at h
  simpa only [row_epi] using h

noncomputable def slack (p : V → ℝ) (i : Fin m) : ℝ :=
  b i - (a i none * (g p).untopD 0 + ∑ v : V, a i (some v) * p v)

lemma slack_nonneg (hrep : HasPolyRep g a b) {p : V → ℝ} (hp : p ∈ DomR g) (i : Fin m) :
    0 ≤ slack g a b p i := by
  have hle : g p ≤ (((g p).untopD 0 : ℝ) : WithTop ℝ) := (coe_untopD hp).ge
  have hi := (hrep p ((g p).untopD 0)).mp hle i
  dsimp [slack]
  linarith

noncomputable def ActiveSet (p : V → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => slack g a b p i = 0)

lemma mem_activeSet_iff {p : V → ℝ} {i : Fin m} :
    i ∈ ActiveSet g a b p ↔
      a i none * (g p).untopD 0 + ∑ v : V, a i (some v) * p v = b i := by
  rw [ActiveSet, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, slack]
  constructor <;> intro h <;> linarith

lemma a_none_nonpos (hrep : HasPolyRep g a b) {p : V → ℝ} (hp : p ∈ DomR g) (i : Fin m) :
    a i none ≤ 0 := by
  by_contra hpos
  push_neg at hpos
  let r := (g p).untopD 0
  let M := (b i - (a i none * r + ∑ v : V, a i (some v) * p v) + 1) / a i none
  have hle : g p ≤ ((r + max M 0 : ℝ) : WithTop ℝ) := by
    rw [← coe_untopD hp, WithTop.coe_le_coe]
    linarith [le_max_right M 0]
  have hi := (hrep p (r + max M 0)).mp hle i
  have hM : M ≤ max M 0 := le_max_left M 0
  have h1 : a i none * M ≤ a i none * max M 0 := mul_le_mul_of_nonneg_left hM hpos.le
  have h2 : a i none * M = b i - (a i none * r + ∑ v : V, a i (some v) * p v) + 1 :=
    mul_div_cancel₀ _ (ne_of_gt hpos)
  linarith

lemma exists_neg_active (hrep : HasPolyRep g a b) {p : V → ℝ} (hp : p ∈ DomR g) :
    ∃ i ∈ ActiveSet g a b p, a i none < 0 := by
  by_contra h
  push_neg at h
  let r := (g p).untopD 0
  let f : Fin m → ℝ := fun i =>
    if a i none < 0 then slack g a b p i / (-a i none) else 1
  have hf : ∀ i : Fin m, 0 < f i := by
    intro i
    dsimp [f]
    split_ifs with ha
    · have hne : slack g a b p i ≠ 0 := by
        intro h0
        have hi : i ∈ ActiveSet g a b p := by simp [ActiveSet, h0]
        linarith [h i hi]
      have hpos : 0 < slack g a b p i :=
        lt_of_le_of_ne (slack_nonneg g a b hrep hp i) hne.symm
      exact div_pos hpos (neg_pos.mpr ha)
    · exact one_pos
  obtain ⟨e, he, heB⟩ := finite_pos_bound Finset.univ f (fun i _ => hf i)
  have hlower : g p ≤ ((r - e : ℝ) : WithTop ℝ) := by
    apply (hrep p (r - e)).mpr
    intro i
    by_cases ha : a i none < 0
    · have hb := heB i (Finset.mem_univ i)
      simp only [f, if_pos ha] at hb
      have hc := (le_div_iff₀ (neg_pos.mpr ha)).mp hb
      dsimp [slack] at hc
      linarith
    · have hc : a i none = 0 := le_antisymm (a_none_nonpos g a b hrep hp i) (not_lt.mp ha)
      have hs := slack_nonneg g a b hrep hp i
      dsimp [slack] at hs
      rw [hc] at hs ⊢
      linarith
  rw [← coe_untopD hp, WithTop.coe_le_coe] at hlower
  linarith

noncomputable def TVal (I : Finset (Fin m)) (d : V → ℝ) : ℝ :=
  if hne : (I.filter (fun i => a i none < 0)).Nonempty then
    (I.filter (fun i => a i none < 0)).sup' hne
      (fun i => (∑ v : V, a i (some v) * d v) / (-a i none))
  else 0

noncomputable def TSet (I : Finset (Fin m)) (d : V → ℝ) : WithTop ℝ :=
  if (I.filter (fun i => a i none < 0)).Nonempty ∧
     (∀ i ∈ I, a i none ≤ 0) ∧
     (∀ i ∈ I, a i none = 0 → ∑ v : V, a i (some v) * d v ≤ 0) then
    ((TVal a I d : ℝ) : WithTop ℝ)
  else ⊤

lemma TSet_le_coe_iff {I : Finset (Fin m)}
    (hne : (I.filter (fun i => a i none < 0)).Nonempty)
    (hle0 : ∀ i ∈ I, a i none ≤ 0) (d : V → ℝ) (dr : ℝ) :
    TSet a I d ≤ (dr : WithTop ℝ) ↔
      ∀ i ∈ I, a i none * dr + ∑ v : V, a i (some v) * d v ≤ 0 := by
  unfold TSet
  split_ifs with hcond
  · rw [WithTop.coe_le_coe]
    unfold TVal
    rw [dif_pos hne, Finset.sup'_le_iff]
    constructor
    · intro h i hi
      rcases lt_or_eq_of_le (hle0 i hi) with hlt | heq
      · have hi' : i ∈ I.filter (fun i => a i none < 0) :=
          Finset.mem_filter.mpr ⟨hi, hlt⟩
        have hdiv := (div_le_iff₀ (neg_pos.mpr hlt)).mp (h i hi')
        linarith
      · have h0 := hcond.2.2 i hi heq
        rw [heq]; linarith
    · intro h i hi
      obtain ⟨hiI, hlt⟩ := Finset.mem_filter.mp hi
      rw [div_le_iff₀ (neg_pos.mpr hlt)]
      linarith [h i hiI]
  · simp only [top_le_iff, WithTop.coe_ne_top, false_iff]
    intro h
    apply hcond
    refine ⟨hne, hle0, fun i hi heq => ?_⟩
    have hi' := h i hi
    rw [heq] at hi'
    linarith

lemma TSet_achieves {I : Finset (Fin m)} {d : V → ℝ} {dr : ℝ}
    (hT : TSet a I d = (dr : WithTop ℝ)) :
    (∀ i ∈ I, a i none * dr + ∑ v : V, a i (some v) * d v ≤ 0) ∧
    ∃ i0 ∈ I, a i0 none < 0 ∧ a i0 none * dr + ∑ v : V, a i0 (some v) * d v = 0 := by
  have hcond : (I.filter (fun i => a i none < 0)).Nonempty ∧
      (∀ i ∈ I, a i none ≤ 0) ∧
      (∀ i ∈ I, a i none = 0 → ∑ v : V, a i (some v) * d v ≤ 0) := by
    by_contra hc
    unfold TSet at hT
    rw [if_neg hc] at hT
    exact WithTop.top_ne_coe hT
  have hle : ∀ i ∈ I, a i none * dr + ∑ v : V, a i (some v) * d v ≤ 0 :=
    (TSet_le_coe_iff a hcond.1 hcond.2.1 d dr).mp hT.le
  refine ⟨hle, ?_⟩
  unfold TSet at hT
  rw [if_pos hcond, WithTop.coe_inj] at hT
  unfold TVal at hT
  rw [dif_pos hcond.1] at hT
  obtain ⟨i0, hi0, hsup⟩ :=
    Finset.exists_mem_eq_sup' hcond.1 (fun i => (∑ v : V, a i (some v) * d v) / (-a i none))
  obtain ⟨hi0I, hlt⟩ := Finset.mem_filter.mp hi0
  refine ⟨i0, hi0I, hlt, ?_⟩
  have h1 : (∑ v : V, a i0 (some v) * d v) / (-a i0 none) = dr := by linarith
  have h2 := (div_eq_iff (ne_of_gt (neg_pos.mpr hlt))).mp h1
  linarith

lemma TSet_subadd {I : Finset (Fin m)}
    (hne : (I.filter (fun i => a i none < 0)).Nonempty)
    (hle0 : ∀ i ∈ I, a i none ≤ 0) (d1 d2 : V → ℝ) :
    TSet a I (fun v => d1 v + d2 v) ≤ TSet a I d1 + TSet a I d2 := by
  by_cases h1 : TSet a I d1 = ⊤
  · simp [h1]
  by_cases h2 : TSet a I d2 = ⊤
  · simp [h2]
  obtain ⟨r1, hr1⟩ := WithTop.ne_top_iff_exists.mp h1
  obtain ⟨r2, hr2⟩ := WithTop.ne_top_iff_exists.mp h2
  rw [← hr1, ← hr2, ← WithTop.coe_add, TSet_le_coe_iff a hne hle0]
  have hle1 := (TSet_le_coe_iff a hne hle0 d1 r1).mp hr1.symm.le
  have hle2 := (TSet_le_coe_iff a hne hle0 d2 r2).mp hr2.symm.le
  intro i hi
  have : (∑ v : V, a i (some v) * (d1 v + d2 v)) =
      (∑ v : V, a i (some v) * d1 v) + (∑ v : V, a i (some v) * d2 v) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  rw [this]
  linarith [hle1 i hi, hle2 i hi]

lemma TSet_mono_subset {I1 I2 : Finset (Fin m)}
    (hsub : I1 ⊆ I2)
    (hne1 : (I1.filter (fun i => a i none < 0)).Nonempty)
    (hle0 : ∀ i ∈ I2, a i none ≤ 0) (d : V → ℝ) :
    TSet a I1 d ≤ TSet a I2 d := by
  by_cases h2 : TSet a I2 d = ⊤
  · simp [h2]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp h2
  have hne2 : (I2.filter (fun i => a i none < 0)).Nonempty := by
    obtain ⟨i, hi⟩ := hne1
    exact ⟨i, Finset.mem_filter.mpr ⟨hsub (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩⟩
  rw [← hr, TSet_le_coe_iff a hne1 (fun i hi => hle0 i (hsub hi))]
  have hle2 := (TSet_le_coe_iff a hne2 hle0 d r).mp hr.symm.le
  exact fun i hi => hle2 i (hsub hi)

noncomputable def T (p : V → ℝ) (d : V → ℝ) : WithTop ℝ :=
  TSet a (ActiveSet g a b p) d

lemma active_neg_nonempty (hrep : HasPolyRep g a b) {p : V → ℝ} (hp : p ∈ DomR g) :
    ((ActiveSet g a b p).filter (fun i => a i none < 0)).Nonempty := by
  obtain ⟨i, hi, hlt⟩ := exists_neg_active g a b hrep hp
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, hlt⟩⟩

lemma T_le_coe_iff (hrep : HasPolyRep g a b) {p : V → ℝ} (hp : p ∈ DomR g)
    (d : V → ℝ) (dr : ℝ) :
    T g a b p d ≤ (dr : WithTop ℝ) ↔
      ∀ i ∈ ActiveSet g a b p, a i none * dr + ∑ v : V, a i (some v) * d v ≤ 0 :=
  TSet_le_coe_iff a (active_neg_nonempty g a b hrep hp)
    (fun i _ => a_none_nonpos g a b hrep hp i) d dr

lemma T_subadd (hrep : HasPolyRep g a b) {p : V → ℝ} (hp : p ∈ DomR g) (d1 d2 : V → ℝ) :
    T g a b p (fun v => d1 v + d2 v) ≤ T g a b p d1 + T g a b p d2 :=
  TSet_subadd a (active_neg_nonempty g a b hrep hp)
    (fun i _ => a_none_nonpos g a b hrep hp i) d1 d2

lemma T_le_of_step (hrep : HasPolyRep g a b) {p : V → ℝ} (hp : p ∈ DomR g)
    {d : V → ℝ} {α : ℝ} (hα : 0 < α) {s : ℝ}
    (hs : g (fun v => p v + α * d v) ≤ (s : WithTop ℝ)) :
    T g a b p d ≤ (((s - (g p).untopD 0) / α : ℝ) : WithTop ℝ) := by
  rw [T_le_coe_iff g a b hrep hp]
  intro i hi
  have hi_eq := (mem_activeSet_iff g a b).mp hi
  have hi_le := (hrep (fun v => p v + α * d v) s).mp hs i
  have hsum : (∑ v : V, a i (some v) * (p v + α * d v)) =
      (∑ v : V, a i (some v) * p v) + α * ∑ v : V, a i (some v) * d v := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  rw [hsum] at hi_le
  have hmul : α * (a i none * ((s - (g p).untopD 0) / α) + ∑ v : V, a i (some v) * d v) ≤ 0 := by
    have h1 : α * (a i none * ((s - (g p).untopD 0) / α)) = a i none * (s - (g p).untopD 0) := by
      calc α * (a i none * ((s - (g p).untopD 0) / α))
          = a i none * (α * ((s - (g p).untopD 0) / α)) := by ring
        _ = a i none * (s - (g p).untopD 0) := by rw [mul_div_cancel₀ _ (ne_of_gt hα)]
    linarith
  exact nonpos_of_mul_nonpos_right hmul hα

lemma ray_exact (hrep : HasPolyRep g a b) {p : V → ℝ} (hp : p ∈ DomR g)
    {d : V → ℝ} {dr : ℝ} (hdr : T g a b p d = (dr : WithTop ℝ)) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ α : ℝ, 0 < α → α ≤ ε0 →
      g (fun v => p v + α * d v) = (((g p).untopD 0 + α * dr : ℝ) : WithTop ℝ) ∧
      ActiveSet g a b (fun v => p v + α * d v) =
        (ActiveSet g a b p).filter (fun i => a i none * dr + ∑ v : V, a i (some v) * d v = 0) := by
  obtain ⟨hle_act, i0, hi0_act, hi0_neg, hi0_eq⟩ := TSet_achieves a hdr
  let f : Fin m → ℝ := fun i =>
    if i ∈ ActiveSet g a b p then 1
    else slack g a b p i / (|a i none * dr + ∑ v : V, a i (some v) * d v| + 1)
  have hf : ∀ i : Fin m, 0 < f i := by
    intro i
    dsimp [f]
    split_ifs with hi
    · exact one_pos
    · have hne : slack g a b p i ≠ 0 := by
        intro h0; exact hi (by simp [ActiveSet, h0])
      have hpos : 0 < slack g a b p i :=
        lt_of_le_of_ne (slack_nonneg g a b hrep hp i) hne.symm
      exact div_pos hpos (by positivity)
  obtain ⟨ε0, hε0, hεB⟩ := finite_pos_bound Finset.univ f (fun i _ => hf i)
  refine ⟨ε0, hε0, fun α hα0 hαε => ?_⟩
  let r := (g p).untopD 0
  have hsum (i : Fin m) : (∑ v : V, a i (some v) * (p v + α * d v)) =
      (∑ v : V, a i (some v) * p v) + α * ∑ v : V, a i (some v) * d v := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => by ring)
  have hinact : ∀ i ∉ ActiveSet g a b p,
      a i none * (r + α * dr) + ∑ v : V, a i (some v) * (p v + α * d v) < b i := by
    intro i hi
    have hb := hεB i (Finset.mem_univ i)
    simp only [f, if_neg hi] at hb
    have hα_le : α ≤ slack g a b p i / (|a i none * dr + ∑ v : V, a i (some v) * d v| + 1) :=
      hαε.trans hb
    have hmul := (le_div_iff₀ (by positivity)).mp hα_le
    have habs := le_abs_self (a i none * dr + ∑ v : V, a i (some v) * d v)
    rw [hsum i]
    dsimp [slack, r] at hmul
    nlinarith
  have hle_g : g (fun v => p v + α * d v) ≤ ((r + α * dr : ℝ) : WithTop ℝ) := by
    apply (hrep _ _).mpr
    intro i
    by_cases hi : i ∈ ActiveSet g a b p
    · have hi_eq := (mem_activeSet_iff g a b).mp hi
      have hi_le := hle_act i hi
      rw [hsum i]
      dsimp [r]
      nlinarith
    · exact (hinact i hi).le
  have hge_g : ((r + α * dr : ℝ) : WithTop ℝ) ≤ g (fun v => p v + α * d v) := by
    by_cases htop : g (fun v => p v + α * d v) = ⊤
    · simp [htop]
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp htop
    rw [← hs, WithTop.coe_le_coe]
    have hi0_s := (hrep _ s).mp hs.symm.le i0
    have hi0_p := (mem_activeSet_iff g a b).mp hi0_act
    rw [hsum i0] at hi0_s
    dsimp [r]
    nlinarith
  have heq_g : g (fun v => p v + α * d v) = ((r + α * dr : ℝ) : WithTop ℝ) :=
    le_antisymm hle_g hge_g
  refine ⟨heq_g, ?_⟩
  ext i
  rw [Finset.mem_filter, mem_activeSet_iff]
  have huntop : (g (fun v => p v + α * d v)).untopD 0 = r + α * dr := by
    rw [heq_g]; rfl
  rw [huntop]
  constructor
  · intro h_eq
    have hi_act : i ∈ ActiveSet g a b p := by
      by_contra hni
      exact (ne_of_lt (hinact i hni)) h_eq
    have hi_p := (mem_activeSet_iff g a b).mp hi_act
    refine ⟨hi_act, ?_⟩
    rw [hsum i] at h_eq
    dsimp [r] at h_eq
    have hmul : α * (a i none * dr + ∑ v : V, a i (some v) * d v) = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hα0)
  · rintro ⟨hi_act, hd_eq⟩
    have hi_p := (mem_activeSet_iff g a b).mp hi_act
    rw [hsum i]
    dsimp [r]
    nlinarith

lemma step_iff_T_add_nonpos (hrep : HasPolyRep g a b) {x y : V → ℝ}
    (hx : x ∈ DomR g) (hy : y ∈ DomR g) (d : V → ℝ) :
    (∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      g x + g y ≥ g (fun w => x w - α * d w) + g (fun w => y w + α * d w)) ↔
    T g a b x (fun w => -d w) + T g a b y d ≤ 0 := by
  constructor
  · rintro ⟨α0, hα0, hstep⟩
    have h1 := hstep α0 hα0.le le_rfl
    obtain ⟨hx', hy'⟩ := ne_top_of_add_le h1 hx hy
    obtain ⟨sx, hsx⟩ := WithTop.ne_top_iff_exists.mp hx'
    obtain ⟨sy, hsy⟩ := WithTop.ne_top_iff_exists.mp hy'
    have hTx : T g a b x (fun w => -d w) ≤ (((sx - (g x).untopD 0) / α0 : ℝ) : WithTop ℝ) := by
      apply T_le_of_step g a b hrep hx hα0
      have heqx : (fun v => x v + α0 * -d v) = (fun w => x w - α0 * d w) := by
        funext w; ring
      rw [heqx]
      exact hsx.symm.le
    have hTy : T g a b y d ≤ (((sy - (g y).untopD 0) / α0 : ℝ) : WithTop ℝ) :=
      T_le_of_step g a b hrep hy hα0 hsy.symm.le
    rw [← hsx, ← hsy, ← coe_untopD hx, ← coe_untopD hy,
        ← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe] at h1
    refine (add_le_add hTx hTy).trans ?_
    rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
    have hdiv : (sx - (g x).untopD 0) / α0 + (sy - (g y).untopD 0) / α0 =
        ((sx + sy) - ((g x).untopD 0 + (g y).untopD 0)) / α0 := by ring
    rw [hdiv]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hα0.le
  · intro hle
    have h0 : (0 : WithTop ℝ) ≠ ⊤ := WithTop.coe_ne_top
    have hne : T g a b x (fun w => -d w) + T g a b y d ≠ ⊤ := ne_top_of_le_ne_top h0 hle
    obtain ⟨hTx, hTy⟩ := WithTop.add_ne_top.mp hne
    obtain ⟨drx, hdrx⟩ := WithTop.ne_top_iff_exists.mp hTx
    obtain ⟨dry, hdry⟩ := WithTop.ne_top_iff_exists.mp hTy
    rw [← hdrx, ← hdry, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at hle
    obtain ⟨εx, hεx, hray_x⟩ := ray_exact g a b hrep hx hdrx.symm
    obtain ⟨εy, hεy, hray_y⟩ := ray_exact g a b hrep hy hdry.symm
    refine ⟨min εx εy, lt_min hεx hεy, fun α hα0 hαm => ?_⟩
    rcases eq_or_lt_of_le hα0 with rfl | hα_pos
    · simp
    have h1 := (hray_x α hα_pos (hαm.trans (min_le_left _ _))).1
    have h2 := (hray_y α hα_pos (hαm.trans (min_le_right _ _))).1
    have heqx : (fun w => x w - α * d w) = (fun w => x w + α * (-d w)) := by
      funext w; ring
    have hgx := coe_untopD hx
    have hgy := coe_untopD hy
    rw [heqx, h1, h2]
    conv_lhs => rw [← hgx, ← hgy]
    rw [← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe]
    nlinarith

noncomputable def gp (p : V → ℝ) (z : V → ℝ) : ℝ :=
  (g z).untopD 0 + ∑ w : V, p w * z w

noncomputable def Tp (p : V → ℝ) (z : V → ℝ) (d : V → ℝ) : WithTop ℝ :=
  T g a b z d + ((∑ w : V, p w * d w : ℝ) : WithTop ℝ)

lemma withTop_add_coe_cancel (A B : WithTop ℝ) (c : ℝ) :
    (A + ((-c : ℝ) : WithTop ℝ)) + (B + (c : WithTop ℝ)) = A + B := by
  cases A <;> cases B <;> simp only [WithTop.top_add, WithTop.add_top, ← WithTop.coe_add]
  exact congrArg WithTop.some (by ring)

lemma withTop_le_zero_of_add_le_zero {A B : WithTop ℝ} (hsum : A + B ≤ 0) (hB : 0 ≤ B) :
    A ≤ 0 := by
  cases A <;> cases B
  · simp at hsum
  · simp at hsum
  · simp at hsum
  · rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at hsum
    rw [← WithTop.coe_zero, WithTop.coe_le_coe] at hB ⊢
    linarith

lemma mnat_exc_T (hrep : HasPolyRep g a b) (hm : MNatExchangeAxiomR g)
    {x y : V → ℝ} (hx : x ∈ DomR g) (hy : y ∈ DomR g) {u : V} (hu : u ∈ SuppPosR x y) :
    T g a b x (fun w => -(CharVec u w : ℝ)) + T g a b y (fun w => (CharVec u w : ℝ)) ≤ 0 ∨
    ∃ v ∈ SuppNegR x y,
      T g a b x (fun w => -(CharVec u w : ℝ) + (CharVec v w : ℝ)) +
      T g a b y (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ)) ≤ 0 := by
  rcases hm x hx y hy u hu with ⟨ut, hvalid, α0, hα0, hstep⟩
  rcases hvalid with rfl | ⟨v, rfl, hv⟩
  · left
    apply (step_iff_T_add_nonpos g a b hrep hx hy (fun w => (CharVec u w : ℝ))).mp
    refine ⟨α0, hα0, fun α hα0 hαm => ?_⟩
    simpa [CharVecOptR] using hstep α hα0 hαm
  · right
    refine ⟨v, hv, ?_⟩
    have h := (step_iff_T_add_nonpos g a b hrep hx hy
      (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ))).mp
      ⟨α0, hα0, fun α hα0 hαm => by simpa [CharVecOptR] using hstep α hα0 hαm⟩
    have heq : (fun w => -((CharVec u w : ℝ) - (CharVec v w : ℝ))) =
        (fun w => -(CharVec u w : ℝ) + (CharVec v w : ℝ)) := by funext w; ring
    rwa [heq] at h

lemma mnat_exc_of_T (hrep : HasPolyRep g a b)
    {x y : V → ℝ} (hx : x ∈ DomR g) (hy : y ∈ DomR g) {u : V}
    (h : T g a b x (fun w => -(CharVec u w : ℝ)) + T g a b y (fun w => (CharVec u w : ℝ)) ≤ 0 ∨
      ∃ v ∈ SuppNegR x y,
        T g a b x (fun w => -(CharVec u w : ℝ) + (CharVec v w : ℝ)) +
        T g a b y (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ)) ≤ 0) :
    ∃ ut : Option V, (ut = none ∨ ∃ v, ut = some v ∧ v ∈ SuppNegR x y) ∧
      ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
        g x + g y ≥ g (fun w => x w - α * (CharVec u w - CharVecOptR ut w)) +
                    g (fun w => y w + α * (CharVec u w - CharVecOptR ut w)) := by
  rcases h with h1 | ⟨v, hv, h2⟩
  · obtain ⟨α0, hα0, hstep⟩ := (step_iff_T_add_nonpos g a b hrep hx hy (fun w => (CharVec u w : ℝ))).mpr h1
    refine ⟨none, Or.inl rfl, α0, hα0, fun α hα0 hαm => ?_⟩
    simpa [CharVecOptR] using hstep α hα0 hαm
  · have heq : (fun w => -(CharVec u w : ℝ) + (CharVec v w : ℝ)) =
        (fun w => -((CharVec u w : ℝ) - (CharVec v w : ℝ))) := by funext w; ring
    rw [heq] at h2
    obtain ⟨α0, hα0, hstep⟩ := (step_iff_T_add_nonpos g a b hrep hx hy
      (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ))).mpr h2
    refine ⟨some v, Or.inr ⟨v, rfl, hv⟩, α0, hα0, fun α hα0 hαm => ?_⟩
    simpa [CharVecOptR] using hstep α hα0 hαm

lemma Tp_add_neg (p : V → ℝ) (x y : V → ℝ) (d : V → ℝ) :
    Tp g a b p x (fun w => -d w) + Tp g a b p y d =
    T g a b x (fun w => -d w) + T g a b y d := by
  dsimp [Tp]
  have hsum : (∑ w : V, p w * -d w) = -(∑ w : V, p w * d w) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  rw [hsum]
  exact withTop_add_coe_cancel _ _ _

lemma closed_sublevel_gp (hrep : HasPolyRep g a b) (p : V → ℝ) (c : ℝ) :
    IsClosed {z : V → ℝ | g z ≤ ((c - ∑ w : V, p w * z w : ℝ) : WithTop ℝ)} := by
  have hset : {z : V → ℝ | g z ≤ ((c - ∑ w : V, p w * z w : ℝ) : WithTop ℝ)} =
      ⋂ i : Fin m, {z : V → ℝ | a i none * (c - ∑ w : V, p w * z w) + ∑ v : V, a i (some v) * z v ≤ b i} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact hrep z (c - ∑ w : V, p w * z w)
  rw [hset]
  apply isClosed_iInter
  intro i
  apply isClosed_le <;> fun_prop

lemma mem_sublevel_gp_iff (p : V → ℝ) (c : ℝ) (z : V → ℝ) :
    g z ≤ ((c - ∑ w : V, p w * z w : ℝ) : WithTop ℝ) ↔ z ∈ DomR g ∧ gp g p z ≤ c := by
  constructor
  · intro h
    have hz : z ∈ DomR g := ne_top_of_le_ne_top WithTop.coe_ne_top h
    refine ⟨hz, ?_⟩
    rw [← coe_untopD hz, WithTop.coe_le_coe] at h
    dsimp [gp]; linarith
  · rintro ⟨hz, hle⟩
    rw [← coe_untopD hz, WithTop.coe_le_coe]
    dsimp [gp] at hle; linarith

lemma ray_gp_nonpos (hrep : HasPolyRep g a b) (p : V → ℝ) {z : V → ℝ} (hz : z ∈ DomR g)
    {d : V → ℝ} (hle : Tp g a b p z d ≤ 0) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ α : ℝ, 0 < α → α ≤ ε0 →
      (fun w => z w + α * d w) ∈ DomR g ∧ gp g p (fun w => z w + α * d w) ≤ gp g p z := by
  have h0 : (0 : WithTop ℝ) ≠ ⊤ := WithTop.coe_ne_top
  have hne : Tp g a b p z d ≠ ⊤ := ne_top_of_le_ne_top h0 hle
  dsimp [Tp] at hne hle
  obtain ⟨hTz, _⟩ := WithTop.add_ne_top.mp hne
  obtain ⟨dr, hdr⟩ := WithTop.ne_top_iff_exists.mp hTz
  rw [← hdr, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at hle
  obtain ⟨ε0, hε0, hray⟩ := ray_exact g a b hrep hz hdr.symm
  refine ⟨ε0, hε0, fun α hα0 hαε => ?_⟩
  have h1 := (hray α hα0 hαε).1
  have hdom : (fun w => z w + α * d w) ∈ DomR g := by
    change g _ ≠ ⊤; rw [h1]; exact WithTop.coe_ne_top
  refine ⟨hdom, ?_⟩
  dsimp [gp]
  have huntop : (g (fun w => z w + α * d w)).untopD 0 = (g z).untopD 0 + α * dr := by
    rw [h1]; rfl
  have hsum : (∑ w : V, p w * (z w + α * d w)) =
      (∑ w : V, p w * z w) + α * ∑ w : V, p w * d w := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  rw [huntop, hsum]
  nlinarith

lemma ray_gp_lt_zero (hrep : HasPolyRep g a b) (p : V → ℝ) {z : V → ℝ} (hz : z ∈ DomR g)
    {d : V → ℝ} (hlt : Tp g a b p z d < 0) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ α : ℝ, 0 < α → α ≤ ε0 →
      (fun w => z w + α * d w) ∈ DomR g ∧ gp g p (fun w => z w + α * d w) < gp g p z := by
  have hne : Tp g a b p z d ≠ ⊤ := ne_top_of_lt hlt
  dsimp [Tp] at hne hlt
  obtain ⟨hTz, _⟩ := WithTop.add_ne_top.mp hne
  obtain ⟨dr, hdr⟩ := WithTop.ne_top_iff_exists.mp hTz
  rw [← hdr, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hlt
  obtain ⟨ε0, hε0, hray⟩ := ray_exact g a b hrep hz hdr.symm
  refine ⟨ε0, hε0, fun α hα0 hαε => ?_⟩
  have h1 := (hray α hα0 hαε).1
  have hdom : (fun w => z w + α * d w) ∈ DomR g := by
    change g _ ≠ ⊤; rw [h1]; exact WithTop.coe_ne_top
  refine ⟨hdom, ?_⟩
  dsimp [gp]
  have huntop : (g (fun w => z w + α * d w)).untopD 0 = (g z).untopD 0 + α * dr := by
    rw [h1]; rfl
  have hsum : (∑ w : V, p w * (z w + α * d w)) =
      (∑ w : V, p w * z w) + α * ∑ w : V, p w * d w := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  rw [huntop, hsum]
  nlinarith

noncomputable def sliceLo (z y : V → ℝ) (u0 : V) (w : V) : ℝ :=
  if w = u0 then y u0 else z w

noncomputable def sliceHi (z y : V → ℝ) (w : V) : ℝ :=
  if w ∈ SuppNegR z y then y w else z w

noncomputable def SliceBox (z y : V → ℝ) (u0 : V) : Set (V → ℝ) :=
  Set.Icc (sliceLo z y u0) (sliceHi z y)

lemma not_mem_suppNeg_of_mem_suppPos {z y : V → ℝ} {u0 : V} (hu0 : u0 ∈ SuppPosR z y) :
    u0 ∉ SuppNegR z y := by
  change y u0 < z u0 at hu0
  change ¬ (z u0 < y u0)
  linarith

lemma self_mem_sliceBox {z y : V → ℝ} {u0 : V} (hu0 : u0 ∈ SuppPosR z y) :
    z ∈ SliceBox z y u0 := by
  have hu0_gt : y u0 < z u0 := by simpa [SuppPosR] using hu0
  constructor <;> intro w
  · dsimp [sliceLo]
    split_ifs with h
    · subst h; exact hu0_gt.le
    · exact le_rfl
  · dsimp [sliceHi]
    split_ifs with h
    · have hw : z w < y w := by simpa [SuppNegR] using h
      exact hw.le
    · exact le_rfl

lemma sliceBox_u0 {z y z' : V → ℝ} {u0 : V} (hu0 : u0 ∈ SuppPosR z y)
    (hz' : z' ∈ SliceBox z y u0) : y u0 ≤ z' u0 ∧ z' u0 ≤ z u0 := by
  have hu0_not_neg := not_mem_suppNeg_of_mem_suppPos hu0
  have h1 := hz'.1 u0
  have h2 := hz'.2 u0
  simp only [sliceLo, if_true] at h1
  simp only [sliceHi, if_neg hu0_not_neg] at h2
  exact ⟨h1, h2⟩

lemma sliceBox_neg {z y z' : V → ℝ} {u0 : V} (hu0 : u0 ∈ SuppPosR z y)
    (hz' : z' ∈ SliceBox z y u0) {v : V} (hv : v ∈ SuppNegR z y) :
    z v ≤ z' v ∧ z' v ≤ y v := by
  have hu0_gt : y u0 < z u0 := by simpa [SuppPosR] using hu0
  have hv_lt : z v < y v := by simpa [SuppNegR] using hv
  have hvu : v ≠ u0 := by intro h; subst h; linarith
  have h1 := hz'.1 v
  have h2 := hz'.2 v
  simp only [sliceLo, if_neg hvu] at h1
  simp only [sliceHi, if_pos hv] at h2
  exact ⟨h1, h2⟩

lemma sliceBox_other {z y z' : V → ℝ} {u0 : V} (hz' : z' ∈ SliceBox z y u0)
    {w : V} (hwu : w ≠ u0) (hwn : w ∉ SuppNegR z y) : z' w = z w := by
  have h1 := hz'.1 w
  have h2 := hz'.2 w
  simp only [sliceLo, if_neg hwu] at h1
  simp only [sliceHi, if_neg hwn] at h2
  exact le_antisymm h2 h1

lemma sliceBox_suppPos_z {z y z' : V → ℝ} {u0 : V} (hu0 : u0 ∈ SuppPosR z y)
    (hz' : z' ∈ SliceBox z y u0) {v : V} (hv : v ∈ SuppPosR z' z) :
    v ∈ SuppNegR z y := by
  have hv_gt : z v < z' v := by simpa [SuppPosR] using hv
  by_contra hnot
  by_cases hvu : v = u0
  · subst v
    have h := (sliceBox_u0 hu0 hz').2
    linarith
  · have h := sliceBox_other hz' hvu hnot
    linarith

lemma sliceBox_suppNeg_z {z y z' : V → ℝ} {u0 : V} (hu0 : u0 ∈ SuppPosR z y)
    (hz' : z' ∈ SliceBox z y u0) {w : V} (hw : w ∈ SuppNegR z' z) :
    w = u0 := by
  have hw_lt : z' w < z w := by simpa [SuppNegR] using hw
  by_contra hwu
  by_cases hwn : w ∈ SuppNegR z y
  · have h := (sliceBox_neg hu0 hz' hwn).1
    linarith
  · have h := sliceBox_other hz' hwu hwn
    linarith

lemma slice_min_at_z (hrep : HasPolyRep g a b) (hm : MNatExchangeAxiomR g)
    {z y : V → ℝ} (hz : z ∈ DomR g) {u0 : V} (hu0 : u0 ∈ SuppPosR z y)
    (p1 : V → ℝ)
    (h_u0 : 0 ≤ Tp g a b p1 z (fun w => -(CharVec u0 w : ℝ)))
    (h_uv : ∀ v ∈ SuppNegR z y, 0 ≤ Tp g a b p1 z (fun w => -(CharVec u0 w : ℝ) + (CharVec v w : ℝ)))
    (h_v : ∀ v ∈ SuppNegR z y, 0 ≤ Tp g a b p1 z (fun w => (CharVec v w : ℝ))) :
    ∀ z' ∈ SliceBox z y u0, z' ∈ DomR g → gp g p1 z ≤ gp g p1 z' := by
  intro y0 hy0_box hy0_dom
  by_contra hnot
  have hlt_y0 : gp g p1 y0 < gp g p1 z := lt_of_not_ge hnot
  let c := gp g p1 y0
  let S := SliceBox z y u0 ∩ {z' : V → ℝ | g z' ≤ ((c - ∑ w : V, p1 w * z' w : ℝ) : WithTop ℝ)}
  have hSne : S.Nonempty := ⟨y0, hy0_box, (mem_sublevel_gp_iff g p1 c y0).mpr ⟨hy0_dom, le_rfl⟩⟩
  have hSc : IsCompact S := isCompact_Icc.inter_right (closed_sublevel_gp g a b hrep p1 c)
  have hcont : Continuous (fun z' : V → ℝ => ∑ w : V, |z' w - z w|) := by fun_prop
  obtain ⟨z', ⟨hz'_box, hz'_sub⟩, hmin⟩ := hSc.exists_isMinOn hSne hcont.continuousOn
  obtain ⟨hz'_dom, hz'_gp⟩ := (mem_sublevel_gp_iff g p1 c z').mp hz'_sub
  have hz'_ne : z' ≠ z := by
    intro heq; subst heq; linarith
  by_cases hpos_ne : (SuppPosR z' z).Nonempty
  · obtain ⟨v, hv_pos⟩ := hpos_ne
    have hv_neg : v ∈ SuppNegR z y := sliceBox_suppPos_z hu0 hz'_box hv_pos
    have hv_gt : z v < z' v := by simpa [SuppPosR] using hv_pos
    have hvu0 : v ≠ u0 := by
      intro h; subst v
      have := (sliceBox_u0 hu0 hz'_box).2
      linarith
    rcases mnat_exc_T g a b hrep hm hz'_dom hz hv_pos with hT_le | ⟨w0, hw0_neg, hT_le⟩
    · rw [← Tp_add_neg g a b p1] at hT_le
      have hTp_z' : Tp g a b p1 z' (fun w => -(CharVec v w : ℝ)) ≤ 0 :=
        withTop_le_zero_of_add_le_zero hT_le (h_v v hv_neg)
      obtain ⟨ε0, hε0, hray⟩ := ray_gp_nonpos g a b hrep p1 hz'_dom hTp_z'
      let t := min ε0 (z' v - z v) / 2
      have ht_pos : 0 < t := by dsimp [t]; positivity
      have ht_ε : t ≤ ε0 := by dsimp [t]; linarith [min_le_left ε0 (z' v - z v)]
      have ht_v : t ≤ z' v - z v := by dsimp [t]; linarith [min_le_right ε0 (z' v - z v)]
      obtain ⟨hz''_dom, hz''_gp⟩ := hray t ht_pos ht_ε
      let z'' : V → ℝ := fun w => z' w + t * -(CharVec v w : ℝ)
      have hz''_box : z'' ∈ SliceBox z y u0 := by
        constructor <;> intro w
        · by_cases hwv : w = v
          · subst w
            simp only [z'', sliceLo, if_neg hvu0, CharVec, if_true, Int.cast_one, mul_neg, mul_one]
            linarith
          · have h1 := hz'_box.1 w
            simpa [z'', CharVec, hwv] using h1
        · by_cases hwv : w = v
          · subst w
            have h2 := hz'_box.2 v
            simp only [z'', sliceHi, if_pos hv_neg, CharVec, if_true, Int.cast_one, mul_neg, mul_one] at h2 ⊢
            linarith
          · have h2 := hz'_box.2 w
            simpa [z'', CharVec, hwv] using h2
      have hz''_S : z'' ∈ S := ⟨hz''_box, (mem_sublevel_gp_iff g p1 c z'').mpr ⟨hz''_dom, hz''_gp.trans hz'_gp⟩⟩
      have hdiff : (∑ w : V, |z'' w - z w|) = (∑ w : V, |z' w - z w|) - t := by
        have hpt (w : V) : |z'' w - z w| = |z' w - z w| - (if w = v then t else 0) := by
          by_cases hwv : w = v
          · subst w
            simp only [z'', CharVec, if_true, Int.cast_one, mul_neg, mul_one]
            rw [abs_of_nonneg (by linarith), abs_of_pos (sub_pos.mpr hv_gt)]
            ring
          · simp [z'', CharVec, hwv]
        simp_rw [hpt]
        rw [Finset.sum_sub_distrib]
        simp
      have hbad : (∑ w : V, |z' w - z w|) ≤ (∑ w : V, |z'' w - z w|) := hmin hz''_S
      linarith
    · have hw0_eq : w0 = u0 := sliceBox_suppNeg_z hu0 hz'_box hw0_neg
      subst w0
      have hu0_lt : z' u0 < z u0 := by simpa [SuppNegR] using hw0_neg
      have heq1 : (fun w => -(CharVec v w : ℝ) + (CharVec u0 w : ℝ)) =
          (fun w => -(-(CharVec u0 w : ℝ) + (CharVec v w : ℝ))) := by funext w; ring
      have heq2 : (fun w => (CharVec v w : ℝ) - (CharVec u0 w : ℝ)) =
          (fun w => -(CharVec u0 w : ℝ) + (CharVec v w : ℝ)) := by funext w; ring
      rw [heq1, heq2, ← Tp_add_neg g a b p1] at hT_le
      have hTp_z' : Tp g a b p1 z' (fun w => -(-(CharVec u0 w : ℝ) + (CharVec v w : ℝ))) ≤ 0 :=
        withTop_le_zero_of_add_le_zero hT_le (h_uv v hv_neg)
      obtain ⟨ε0, hε0, hray⟩ := ray_gp_nonpos g a b hrep p1 hz'_dom hTp_z'
      let t := min ε0 (min (z' v - z v) (z u0 - z' u0)) / 2
      have ht_pos : 0 < t := by dsimp [t]; positivity
      have ht_ε : t ≤ ε0 := by dsimp [t]; linarith [min_le_left ε0 (min (z' v - z v) (z u0 - z' u0))]
      have ht_v : t ≤ z' v - z v := by
        have := (min_le_right ε0 (min (z' v - z v) (z u0 - z' u0))).trans (min_le_left _ _)
        dsimp [t]; linarith
      have ht_u0 : t ≤ z u0 - z' u0 := by
        have := (min_le_right ε0 (min (z' v - z v) (z u0 - z' u0))).trans (min_le_right _ _)
        dsimp [t]; linarith
      obtain ⟨hz''_dom, hz''_gp⟩ := hray t ht_pos ht_ε
      let z'' : V → ℝ := fun w => z' w + t * -(-(CharVec u0 w : ℝ) + (CharVec v w : ℝ))
      have hz''_box : z'' ∈ SliceBox z y u0 := by
        constructor <;> intro w
        · by_cases hwv : w = v
          · subst w
            simp only [z'', sliceLo, if_neg hvu0, CharVec, if_true, if_neg (Ne.symm hvu0), Int.cast_one, Int.cast_zero, neg_zero, zero_add, mul_neg, mul_one]
            linarith
          · by_cases hwu0 : w = u0
            · subst w
              have h1 := hz'_box.1 u0
              simp only [z'', sliceLo, if_true, CharVec, if_neg hwv, Int.cast_one, Int.cast_zero, add_zero, neg_neg, mul_one] at h1 ⊢
              linarith
            · have h1 := hz'_box.1 w
              simpa [z'', CharVec, hwv, hwu0] using h1
        · by_cases hwv : w = v
          · subst w
            have h2 := hz'_box.2 v
            simp only [z'', sliceHi, if_pos hv_neg, CharVec, if_true, if_neg hvu0, Int.cast_one, Int.cast_zero, neg_zero, zero_add, mul_neg, mul_one] at h2 ⊢
            linarith
          · by_cases hwu0 : w = u0
            · subst w
              have hu0_not_neg := not_mem_suppNeg_of_mem_suppPos hu0
              simp only [z'', sliceHi, if_neg hu0_not_neg, CharVec, if_true, if_neg hwv, Int.cast_one, Int.cast_zero, add_zero, neg_neg, mul_one]
              linarith
            · have h2 := hz'_box.2 w
              simpa [z'', CharVec, hwv, hwu0] using h2
      have hz''_S : z'' ∈ S := ⟨hz''_box, (mem_sublevel_gp_iff g p1 c z'').mpr ⟨hz''_dom, hz''_gp.trans hz'_gp⟩⟩
      have hdiff : (∑ w : V, |z'' w - z w|) = (∑ w : V, |z' w - z w|) - 2 * t := by
        have hpt (w : V) : |z'' w - z w| = |z' w - z w| - (if w = v then t else 0) - (if w = u0 then t else 0) := by
          by_cases hwv : w = v
          · subst w
            simp only [z'', CharVec, if_true, if_neg hvu0, Int.cast_one, Int.cast_zero, neg_zero, zero_add, mul_neg, mul_one]
            rw [abs_of_nonneg (by linarith), abs_of_pos (sub_pos.mpr hv_gt)]
            ring
          · by_cases hwu0 : w = u0
            · subst w
              simp only [z'', CharVec, if_true, if_neg hwv, Int.cast_one, Int.cast_zero, add_zero, neg_neg, mul_one]
              rw [abs_of_nonpos (by linarith), abs_of_neg (sub_neg.mpr hu0_lt)]
              ring
            · simp [z'', CharVec, hwv, hwu0]
        simp_rw [hpt]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
        simp
        ring
      have hbad : (∑ w : V, |z' w - z w|) ≤ (∑ w : V, |z'' w - z w|) := hmin hz''_S
      linarith
  · have hpos_empty : SuppPosR z' z = ∅ := Set.not_nonempty_iff_eq_empty.mp hpos_ne
    have hle_all : ∀ w : V, z' w ≤ z w := by
      intro w
      by_contra hlt
      push_neg at hlt
      have hw : w ∈ SuppPosR z' z := hlt
      rw [hpos_empty] at hw
      exact Set.notMem_empty w hw
    have hex_lt : ∃ w : V, z' w < z w := by
      by_contra hall
      push_neg at hall
      apply hz'_ne
      funext w
      exact le_antisymm (hle_all w) (hall w)
    obtain ⟨w0, hw0⟩ := hex_lt
    have hw0_neg : w0 ∈ SuppNegR z' z := hw0
    have hw0_eq : w0 = u0 := sliceBox_suppNeg_z hu0 hz'_box hw0_neg
    subst w0
    have hu0_pos : u0 ∈ SuppPosR z z' := hw0
    rcases mnat_exc_T g a b hrep hm hz hz'_dom hu0_pos with hT_le | ⟨v0, hv0_neg, _⟩
    · rw [← Tp_add_neg g a b p1] at hT_le
      have hTp_z' : Tp g a b p1 z' (fun w => (CharVec u0 w : ℝ)) ≤ 0 := by
        rw [add_comm] at hT_le
        exact withTop_le_zero_of_add_le_zero hT_le h_u0
      obtain ⟨ε0, hε0, hray⟩ := ray_gp_nonpos g a b hrep p1 hz'_dom hTp_z'
      let t := min ε0 (z u0 - z' u0) / 2
      have ht_pos : 0 < t := by dsimp [t]; positivity
      have ht_ε : t ≤ ε0 := by dsimp [t]; linarith [min_le_left ε0 (z u0 - z' u0)]
      have ht_u0 : t ≤ z u0 - z' u0 := by dsimp [t]; linarith [min_le_right ε0 (z u0 - z' u0)]
      obtain ⟨hz''_dom, hz''_gp⟩ := hray t ht_pos ht_ε
      let z'' : V → ℝ := fun w => z' w + t * (CharVec u0 w : ℝ)
      have hz''_box : z'' ∈ SliceBox z y u0 := by
        constructor <;> intro w
        · by_cases hwu0 : w = u0
          · subst w
            have h1 := hz'_box.1 u0
            simp only [z'', sliceLo, if_true, CharVec, Int.cast_one, mul_one] at h1 ⊢
            linarith
          · have h1 := hz'_box.1 w
            simpa [z'', CharVec, hwu0] using h1
        · by_cases hwu0 : w = u0
          · subst w
            have hu0_not_neg := not_mem_suppNeg_of_mem_suppPos hu0
            simp only [z'', sliceHi, if_neg hu0_not_neg, CharVec, if_true, Int.cast_one, mul_one]
            linarith
          · have h2 := hz'_box.2 w
            simpa [z'', CharVec, hwu0] using h2
      have hz''_S : z'' ∈ S := ⟨hz''_box, (mem_sublevel_gp_iff g p1 c z'').mpr ⟨hz''_dom, hz''_gp.trans hz'_gp⟩⟩
      have hdiff : (∑ w : V, |z'' w - z w|) = (∑ w : V, |z' w - z w|) - t := by
        have hpt (w : V) : |z'' w - z w| = |z' w - z w| - (if w = u0 then t else 0) := by
          by_cases hwu0 : w = u0
          · subst w
            simp only [z'', CharVec, if_true, Int.cast_one, mul_one]
            rw [abs_of_nonpos (by linarith), abs_of_neg (sub_neg.mpr hw0)]
            ring
          · simp [z'', CharVec, hwu0]
        simp_rw [hpt]
        rw [Finset.sum_sub_distrib]
        simp
      have hbad : (∑ w : V, |z' w - z w|) ≤ (∑ w : V, |z'' w - z w|) := hmin hz''_S
      linarith
    · have hv0_pos : v0 ∈ SuppPosR z' z := hv0_neg
      rw [hpos_empty] at hv0_pos
      exact (Set.notMem_empty v0 hv0_pos).elim

lemma sum_charVec_mul (p : V → ℝ) (u : V) :
    (∑ w : V, p w * (CharVec u w : ℝ)) = p u := by
  have hpt (w : V) : p w * (CharVec u w : ℝ) = if w = u then p u else 0 := by
    dsimp [CharVec]; split_ifs with h
    · subst h; ring
    · ring
  simp_rw [hpt]
  simp

lemma sum_charVec_neg_mul (p : V → ℝ) (u : V) :
    (∑ w : V, p w * -(CharVec u w : ℝ)) = -p u := by
  have hpt (w : V) : p w * -(CharVec u w : ℝ) = -(p w * (CharVec u w : ℝ)) := by ring
  simp_rw [hpt]
  rw [Finset.sum_neg_distrib, sum_charVec_mul]

noncomputable def suppPosFin (x y : V → ℝ) : Finset V :=
  Finset.univ.filter (fun v => y v < x v)

noncomputable def suppNegFin (x y : V → ℝ) : Finset V :=
  Finset.univ.filter (fun v => x v < y v)

lemma mem_suppPosFin {x y : V → ℝ} {v : V} : v ∈ suppPosFin x y ↔ v ∈ SuppPosR x y := by
  simp [suppPosFin, SuppPosR]

lemma mem_suppNegFin {x y : V → ℝ} {v : V} : v ∈ suppNegFin x y ↔ v ∈ SuppNegR x y := by
  simp [suppNegFin, SuppNegR]

noncomputable def cValFrom (p0 : V → ℝ) (u0 : V) (A : Finset (Fin m)) (N : Finset V) : WithTop ℝ :=
  min (TSet a A (fun w => -(CharVec u0 w : ℝ)) + ((∑ w : V, p0 w * -(CharVec u0 w : ℝ) : ℝ) : WithTop ℝ))
    (N.inf (fun v => TSet a A (fun w => -(CharVec u0 w : ℝ) + (CharVec v w : ℝ)) +
      ((∑ w : V, p0 w * (-(CharVec u0 w : ℝ) + (CharVec v w : ℝ)) : ℝ) : WithTop ℝ)))

noncomputable def cVal (p0 : V → ℝ) (z y : V → ℝ) (u0 : V) : WithTop ℝ :=
  cValFrom a p0 u0 (ActiveSet g a b z) (suppNegFin z y)

lemma cVal_eq (p0 : V → ℝ) (z y : V → ℝ) (u0 : V) :
    cVal g a b p0 z y u0 =
    min (Tp g a b p0 z (fun w => -(CharVec u0 w : ℝ)))
      ((suppNegFin z y).inf (fun v => Tp g a b p0 z (fun w => -(CharVec u0 w : ℝ) + (CharVec v w : ℝ)))) :=
  rfl

noncomputable def cValSet (p0 : V → ℝ) (u0 : V) : Finset (WithTop ℝ) :=
  (Finset.univ ×ˢ Finset.univ).image (fun p : Finset (Fin m) × Finset V => cValFrom a p0 u0 p.1 p.2)

lemma cVal_mem_cValSet (p0 : V → ℝ) (z y : V → ℝ) (u0 : V) :
    cVal g a b p0 z y u0 ∈ cValSet a p0 u0 := by
  rw [cVal, cValSet, Finset.mem_image]
  exact ⟨(ActiveSet g a b z, suppNegFin z y), by simp, rfl⟩

noncomputable def cValRank (p0 : V → ℝ) (z y : V → ℝ) (u0 : V) : ℕ :=
  ((cValSet a p0 u0).filter (fun val => cVal g a b p0 z y u0 < val)).card

lemma cValRank_lt_of_cVal_lt (p0 : V → ℝ) {z zStar y : V → ℝ} {u0 : V}
    (hlt : cVal g a b p0 z y u0 < cVal g a b p0 zStar y u0) :
    cValRank g a b p0 zStar y u0 < cValRank g a b p0 z y u0 := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro val hval
    rw [Finset.mem_filter] at hval ⊢
    exact ⟨hval.1, lt_trans hlt hval.2⟩
  · intro heq
    have hmem : cVal g a b p0 zStar y u0 ∈ (cValSet a p0 u0).filter (fun val => cVal g a b p0 z y u0 < val) :=
      Finset.mem_filter.mpr ⟨cVal_mem_cValSet g a b p0 zStar y u0, hlt⟩
    rw [← heq, Finset.mem_filter] at hmem
    exact (lt_irrefl _ hmem.2).elim

noncomputable def shiftPrice (p0 : V → ℝ) (u0 : V) (c : ℝ) (w : V) : ℝ :=
  p0 w + if w = u0 then c else 0

lemma sum_shiftPrice_mul (p0 : V → ℝ) (u0 : V) (c : ℝ) (d : V → ℝ) :
    (∑ w : V, shiftPrice p0 u0 c w * d w) = (∑ w : V, p0 w * d w) + c * d u0 := by
  have hpt (w : V) : shiftPrice p0 u0 c w * d w = p0 w * d w + (if w = u0 then c * d w else 0) := by
    dsimp [shiftPrice]; split_ifs <;> ring
  simp_rw [hpt]
  rw [Finset.sum_add_distrib]
  simp

lemma Tp_shiftPrice (p0 : V → ℝ) (u0 : V) (c : ℝ) (z : V → ℝ) (d : V → ℝ)
    {s : ℝ} (hs : c * d u0 = s) :
    Tp g a b (shiftPrice p0 u0 c) z d = Tp g a b p0 z d + (s : WithTop ℝ) := by
  dsimp [Tp]
  rw [sum_shiftPrice_mul, hs, WithTop.coe_add, ← add_assoc]

lemma withTop_nonneg_of_coe_le {A : WithTop ℝ} {c : ℝ} (h : (c : WithTop ℝ) ≤ A) :
    0 ≤ A + ((-c : ℝ) : WithTop ℝ) := by
  cases A with
  | top => simp
  | coe r =>
    rw [WithTop.coe_le_coe] at h
    rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
    linarith

lemma withTop_coe_lt_of_pos {A : WithTop ℝ} {c : ℝ} (h : 0 < A + ((-c : ℝ) : WithTop ℝ)) :
    (c : WithTop ℝ) < A := by
  cases A with
  | top => exact WithTop.coe_lt_top c
  | coe r =>
    rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h
    rw [WithTop.coe_lt_coe]
    linarith

lemma slice_step_min (hrep : HasPolyRep g a b) (hm : MNatExchangeAxiomR g)
    (p0 : V → ℝ) {z y : V → ℝ} (hz : z ∈ DomR g) (hy : y ∈ DomR g)
    {u0 : V} (hu0 : u0 ∈ SuppPosR z y)
    (h_v0 : ∀ v ∈ SuppNegR z y, 0 ≤ Tp g a b p0 z (fun w => (CharVec v w : ℝ))) :
    ∃ zStar : V → ℝ,
      zStar ∈ DomR g ∧
      (∑ w : V, zStar w ≤ ∑ w : V, z w) ∧
      SuppPosR zStar y ⊆ SuppPosR z y ∧
      SuppNegR zStar y ⊆ SuppNegR z y ∧
      (∀ v ∈ SuppNegR zStar y, 0 ≤ Tp g a b p0 zStar (fun w => (CharVec v w : ℝ))) ∧
      ((suppPosFin zStar y).card < (suppPosFin z y).card ∨
        (u0 ∈ SuppPosR zStar y ∧ cValRank g a b p0 zStar y u0 < cValRank g a b p0 z y u0)) := by
  have hc_ne_top : cVal g a b p0 z y u0 ≠ ⊤ := by
    have h0 : (0 : WithTop ℝ) ≠ ⊤ := WithTop.coe_ne_top
    rcases mnat_exc_T g a b hrep hm hz hy hu0 with hT1 | ⟨v, hv, hT2⟩
    · have hne1 : T g a b z (fun w => -(CharVec u0 w : ℝ)) ≠ ⊤ :=
        (WithTop.add_ne_top.mp (ne_top_of_le_ne_top h0 hT1)).1
      have hTp1 : Tp g a b p0 z (fun w => -(CharVec u0 w : ℝ)) ≠ ⊤ :=
        WithTop.add_ne_top.mpr ⟨hne1, WithTop.coe_ne_top⟩
      exact ne_top_of_le_ne_top hTp1 (min_le_left _ _)
    · have hne2 : T g a b z (fun w => -(CharVec u0 w : ℝ) + (CharVec v w : ℝ)) ≠ ⊤ :=
        (WithTop.add_ne_top.mp (ne_top_of_le_ne_top h0 hT2)).1
      have hTp2 : Tp g a b p0 z (fun w => -(CharVec u0 w : ℝ) + (CharVec v w : ℝ)) ≠ ⊤ :=
        WithTop.add_ne_top.mpr ⟨hne2, WithTop.coe_ne_top⟩
      have hv_fin : v ∈ suppNegFin z y := mem_suppNegFin.mpr hv
      have hle : cVal g a b p0 z y u0 ≤ Tp g a b p0 z (fun w => -(CharVec u0 w : ℝ) + (CharVec v w : ℝ)) :=
        (min_le_right _ _).trans (Finset.inf_le hv_fin)
      exact ne_top_of_le_ne_top hTp2 hle
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hc_ne_top
  let p1 := shiftPrice p0 u0 c
  have hTp_u0_eq (z' : V → ℝ) :
      Tp g a b p1 z' (fun w => -(CharVec u0 w : ℝ)) =
      Tp g a b p0 z' (fun w => -(CharVec u0 w : ℝ)) + ((-c : ℝ) : WithTop ℝ) :=
    Tp_shiftPrice g a b p0 u0 c z' _ (by simp [CharVec])
  have hTp_uv_eq (z' : V → ℝ) {v : V} (hvu0 : v ≠ u0) :
      Tp g a b p1 z' (fun w => -(CharVec u0 w : ℝ) + (CharVec v w : ℝ)) =
      Tp g a b p0 z' (fun w => -(CharVec u0 w : ℝ) + (CharVec v w : ℝ)) + ((-c : ℝ) : WithTop ℝ) :=
    Tp_shiftPrice g a b p0 u0 c z' _ (by simp [CharVec, Ne.symm hvu0])
  have hTp_v_eq (z' : V → ℝ) {v : V} (hvu0 : v ≠ u0) :
      Tp g a b p1 z' (fun w => (CharVec v w : ℝ)) =
      Tp g a b p0 z' (fun w => (CharVec v w : ℝ)) := by
    have h := Tp_shiftPrice g a b p0 u0 c z' (fun w => (CharVec v w : ℝ)) (s := 0)
      (by simp [CharVec, Ne.symm hvu0])
    simpa using h
  have h_u0 : 0 ≤ Tp g a b p1 z (fun w => -(CharVec u0 w : ℝ)) := by
    rw [hTp_u0_eq]
    apply withTop_nonneg_of_coe_le
    rw [hc, cVal_eq]
    exact min_le_left _ _
  have h_uv : ∀ v ∈ SuppNegR z y, 0 ≤ Tp g a b p1 z (fun w => -(CharVec u0 w : ℝ) + (CharVec v w : ℝ)) := by
    intro v hv
    have hu0_gt : y u0 < z u0 := hu0
    have hv_lt : z v < y v := hv
    have hvu0 : v ≠ u0 := by intro h; subst v; linarith
    rw [hTp_uv_eq z hvu0]
    apply withTop_nonneg_of_coe_le
    rw [hc, cVal_eq]
    exact (min_le_right _ _).trans (Finset.inf_le (mem_suppNegFin.mpr hv))
  have h_v : ∀ v ∈ SuppNegR z y, 0 ≤ Tp g a b p1 z (fun w => (CharVec v w : ℝ)) := by
    intro v hv
    have hu0_gt : y u0 < z u0 := hu0
    have hv_lt : z v < y v := hv
    have hvu0 : v ≠ u0 := by intro h; subst v; linarith
    rw [hTp_v_eq z hvu0]
    exact h_v0 v hv
  have hslice_min := slice_min_at_z g a b hrep hm hz hu0 p1 h_u0 h_uv h_v
  let c0 := gp g p1 z
  let M := SliceBox z y u0 ∩
    ({z' : V → ℝ | ∑ w : V, z' w ≤ ∑ w : V, z w} ∩
     {z' : V → ℝ | g z' ≤ ((c0 - ∑ w : V, p1 w * z' w : ℝ) : WithTop ℝ)})
  have hMne : M.Nonempty := ⟨z, self_mem_sliceBox hu0,
    show ∑ w : V, z w ≤ ∑ w : V, z w from le_rfl,
    (mem_sublevel_gp_iff g p1 c0 z).mpr ⟨hz, le_rfl⟩⟩
  have hMc : IsCompact M := by
    apply isCompact_Icc.inter_right
    apply IsClosed.inter
    · apply isClosed_le <;> fun_prop
    · exact closed_sublevel_gp g a b hrep p1 c0
  have hcont_u0 : Continuous (fun z' : V → ℝ => z' u0) := by fun_prop
  obtain ⟨zStar, ⟨hzS_box, hzS_sum, hzS_sub⟩, hmin_u0⟩ := hMc.exists_isMinOn hMne hcont_u0.continuousOn
  change ∑ w : V, zStar w ≤ ∑ w : V, z w at hzS_sum
  obtain ⟨hzS_dom, hzS_gp_le⟩ := (mem_sublevel_gp_iff g p1 c0 zStar).mp hzS_sub
  have hzS_gp_eq : gp g p1 zStar = c0 := le_antisymm hzS_gp_le (hslice_min zStar hzS_box hzS_dom)
  have hpos_sub : SuppPosR zStar y ⊆ SuppPosR z y := by
    intro w hw
    change y w < zStar w at hw
    by_cases hwu0 : w = u0
    · subst w; exact hu0
    · by_cases hwn : w ∈ SuppNegR z y
      · have h := (sliceBox_neg hu0 hzS_box hwn).2
        linarith
      · have h := sliceBox_other hzS_box hwu0 hwn
        change y w < z w
        linarith
  have hneg_sub : SuppNegR zStar y ⊆ SuppNegR z y := by
    intro w hw
    change zStar w < y w at hw
    by_cases hwu0 : w = u0
    · subst w
      have h := (sliceBox_u0 hu0 hzS_box).1
      linarith
    · by_cases hwn : w ∈ SuppNegR z y
      · exact hwn
      · have h := sliceBox_other hzS_box hwu0 hwn
        change z w < y w
        linarith
  have hzS_v0 : ∀ v ∈ SuppNegR zStar y, 0 ≤ Tp g a b p0 zStar (fun w => (CharVec v w : ℝ)) := by
    intro v hv
    have hv_z : v ∈ SuppNegR z y := hneg_sub hv
    have hu0_gt : y u0 < z u0 := hu0
    have hv_lt : zStar v < y v := hv
    have hvu0 : v ≠ u0 := by
      intro h; subst v
      have := not_mem_suppNeg_of_mem_suppPos hu0
      exact this hv_z
    rw [← hTp_v_eq zStar hvu0]
    by_contra hlt
    push_neg at hlt
    obtain ⟨ε0, hε0, hray⟩ := ray_gp_lt_zero g a b hrep p1 hzS_dom hlt
    let t := min ε0 (y v - zStar v) / 2
    have ht_pos : 0 < t := by dsimp [t]; positivity
    have ht_ε : t ≤ ε0 := by dsimp [t]; linarith [min_le_left ε0 (y v - zStar v)]
    have ht_v : t ≤ y v - zStar v := by dsimp [t]; linarith [min_le_right ε0 (y v - zStar v)]
    obtain ⟨hz''_dom, hz''_gp⟩ := hray t ht_pos ht_ε
    let z'' : V → ℝ := fun w => zStar w + t * (CharVec v w : ℝ)
    have hz''_box : z'' ∈ SliceBox z y u0 := by
      constructor <;> intro w
      · by_cases hwv : w = v
        · subst w
          have h1 := hzS_box.1 v
          simp only [z'', sliceLo, if_neg hvu0, CharVec, if_true, Int.cast_one, mul_one] at h1 ⊢
          linarith
        · have h1 := hzS_box.1 w
          simpa [z'', CharVec, hwv] using h1
      · by_cases hwv : w = v
        · subst w
          simp only [z'', sliceHi, if_pos hv_z, CharVec, if_true, Int.cast_one, mul_one]
          linarith
        · have h2 := hzS_box.2 w
          simpa [z'', CharVec, hwv] using h2
    have hge := hslice_min z'' hz''_box hz''_dom
    linarith
  refine ⟨zStar, hzS_dom, hzS_sum, hpos_sub, hneg_sub, hzS_v0, ?_⟩
  have hu0_bounds := sliceBox_u0 hu0 hzS_box
  rcases eq_or_lt_of_le hu0_bounds.1 with heq_u0 | hlt_u0
  · left
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro w hw
      exact mem_suppPosFin.mpr (hpos_sub (mem_suppPosFin.mp hw))
    · intro heq
      have hu0_in : u0 ∈ suppPosFin z y := mem_suppPosFin.mpr hu0
      rw [← heq, mem_suppPosFin] at hu0_in
      change y u0 < zStar u0 at hu0_in
      linarith
  · right
    have hu0_posS : u0 ∈ SuppPosR zStar y := hlt_u0
    refine ⟨hu0_posS, cValRank_lt_of_cVal_lt g a b p0 ?_⟩
    rw [← hc, cVal_eq, lt_min_iff]
    refine ⟨?_, ?_⟩
    · apply withTop_coe_lt_of_pos
      rw [← hTp_u0_eq]
      by_contra hle
      push_neg at hle
      obtain ⟨ε0, hε0, hray⟩ := ray_gp_nonpos g a b hrep p1 hzS_dom hle
      let t := min ε0 (zStar u0 - y u0) / 2
      have ht_pos : 0 < t := by dsimp [t]; positivity
      have ht_ε : t ≤ ε0 := by dsimp [t]; linarith [min_le_left ε0 (zStar u0 - y u0)]
      have ht_u0 : t ≤ zStar u0 - y u0 := by dsimp [t]; linarith [min_le_right ε0 (zStar u0 - y u0)]
      obtain ⟨hz''_dom, hz''_gp⟩ := hray t ht_pos ht_ε
      let z'' : V → ℝ := fun w => zStar w + t * -(CharVec u0 w : ℝ)
      have hz''_box : z'' ∈ SliceBox z y u0 := by
        constructor <;> intro w
        · by_cases hwu0 : w = u0
          · subst w
            simp only [z'', sliceLo, if_true, CharVec, Int.cast_one, mul_neg, mul_one]
            linarith
          · have h1 := hzS_box.1 w
            simpa [z'', CharVec, hwu0] using h1
        · by_cases hwu0 : w = u0
          · subst w
            have hu0_not_neg := not_mem_suppNeg_of_mem_suppPos hu0
            have h2 := hzS_box.2 u0
            simp only [z'', sliceHi, if_neg hu0_not_neg, CharVec, if_true, Int.cast_one, mul_neg, mul_one] at h2 ⊢
            linarith
          · have h2 := hzS_box.2 w
            simpa [z'', CharVec, hwu0] using h2
      have hz''_sum : ∑ w : V, z'' w ≤ ∑ w : V, z w := by
        have hsum_eq : (∑ w : V, z'' w) = (∑ w : V, zStar w) - t := by
          have hpt (w : V) : z'' w = zStar w - (if w = u0 then t else 0) := by
            by_cases hwu0 : w = u0
            · subst w; simp only [z'', CharVec, if_true, Int.cast_one]; ring
            · simp [z'', CharVec, hwu0]
          simp_rw [hpt]
          rw [Finset.sum_sub_distrib]
          simp
        linarith
      have hz''_M : z'' ∈ M := ⟨hz''_box, hz''_sum,
        (mem_sublevel_gp_iff g p1 c0 z'').mpr ⟨hz''_dom, hz''_gp.trans hzS_gp_le⟩⟩
      have hmin_le : zStar u0 ≤ z'' u0 := hmin_u0 hz''_M
      have hz''_u0 : z'' u0 = zStar u0 - t := by simp [z'', CharVec]; ring
      linarith
    · rw [Finset.lt_inf_iff (WithTop.coe_lt_top c)]
      intro v hv_fin
      have hv : v ∈ SuppNegR zStar y := mem_suppNegFin.mp hv_fin
      have hv_z : v ∈ SuppNegR z y := hneg_sub hv
      have hv_lt : zStar v < y v := hv
      have hvu0 : v ≠ u0 := by
        intro h; subst v
        exact (not_mem_suppNeg_of_mem_suppPos hu0) hv_z
      apply withTop_coe_lt_of_pos
      rw [← hTp_uv_eq zStar hvu0]
      by_contra hle
      push_neg at hle
      obtain ⟨ε0, hε0, hray⟩ := ray_gp_nonpos g a b hrep p1 hzS_dom hle
      let t := min ε0 (min (zStar u0 - y u0) (y v - zStar v)) / 2
      have ht_pos : 0 < t := by dsimp [t]; positivity
      have ht_ε : t ≤ ε0 := by dsimp [t]; linarith [min_le_left ε0 (min (zStar u0 - y u0) (y v - zStar v))]
      have ht_u0 : t ≤ zStar u0 - y u0 := by
        have := (min_le_right ε0 (min (zStar u0 - y u0) (y v - zStar v))).trans (min_le_left _ _)
        dsimp [t]; linarith
      have ht_v : t ≤ y v - zStar v := by
        have := (min_le_right ε0 (min (zStar u0 - y u0) (y v - zStar v))).trans (min_le_right _ _)
        dsimp [t]; linarith
      obtain ⟨hz''_dom, hz''_gp⟩ := hray t ht_pos ht_ε
      let z'' : V → ℝ := fun w => zStar w + t * (-(CharVec u0 w : ℝ) + (CharVec v w : ℝ))
      have hz''_box : z'' ∈ SliceBox z y u0 := by
        constructor <;> intro w
        · by_cases hwu0 : w = u0
          · subst w
            simp only [z'', sliceLo, if_true, CharVec, if_neg (Ne.symm hvu0), Int.cast_one, Int.cast_zero, add_zero, mul_neg, mul_one]
            linarith
          · by_cases hwv : w = v
            · subst w
              have h1 := hzS_box.1 v
              simp only [z'', sliceLo, if_neg hwu0, CharVec, if_true, Int.cast_one, Int.cast_zero, neg_zero, zero_add, mul_one] at h1 ⊢
              linarith
            · have h1 := hzS_box.1 w
              simpa [z'', CharVec, hwu0, hwv] using h1
        · by_cases hwu0 : w = u0
          · subst w
            have hu0_not_neg := not_mem_suppNeg_of_mem_suppPos hu0
            have h2 := hzS_box.2 u0
            simp only [z'', sliceHi, if_neg hu0_not_neg, CharVec, if_true, if_neg (Ne.symm hvu0), Int.cast_one, Int.cast_zero, add_zero, mul_neg, mul_one] at h2 ⊢
            linarith
          · by_cases hwv : w = v
            · subst w
              simp only [z'', sliceHi, if_pos hv_z, CharVec, if_neg hwu0, if_true, Int.cast_one, Int.cast_zero, neg_zero, zero_add, mul_one]
              linarith
            · have h2 := hzS_box.2 w
              simpa [z'', CharVec, hwu0, hwv] using h2
      have hz''_sum : ∑ w : V, z'' w ≤ ∑ w : V, z w := by
        have hsum_eq : (∑ w : V, z'' w) = ∑ w : V, zStar w := by
          have hpt (w : V) : z'' w = zStar w - (if w = u0 then t else 0) + (if w = v then t else 0) := by
            by_cases hwu0 : w = u0
            · subst w
              simp only [z'', CharVec, if_true, if_neg (Ne.symm hvu0), Int.cast_one, Int.cast_zero, add_zero]
              ring
            · by_cases hwv : w = v
              · subst w
                simp only [z'', CharVec, if_neg hwu0, if_true, Int.cast_one, Int.cast_zero, neg_zero, zero_add]
                ring
              · simp [z'', CharVec, hwu0, hwv]
          simp_rw [hpt]
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          simp
        linarith
      have hz''_M : z'' ∈ M := ⟨hz''_box, hz''_sum,
        (mem_sublevel_gp_iff g p1 c0 z'').mpr ⟨hz''_dom, hz''_gp.trans hzS_gp_le⟩⟩
      have hmin_le : zStar u0 ≤ z'' u0 := hmin_u0 hz''_M
      have hz''_u0 : z'' u0 = zStar u0 - t := by
        simp only [z'', CharVec, if_true, if_neg (Ne.symm hvu0), Int.cast_one, Int.cast_zero, add_zero]
        ring
      linarith

lemma slice_reduce_card (hrep : HasPolyRep g a b) (hm : MNatExchangeAxiomR g)
    (p0 : V → ℝ) (y : V → ℝ) (hy : y ∈ DomR g) (u0 : V) :
    ∀ r : ℕ, ∀ z : V → ℝ,
      z ∈ DomR g →
      u0 ∈ SuppPosR z y →
      (∀ v ∈ SuppNegR z y, 0 ≤ Tp g a b p0 z (fun w => (CharVec v w : ℝ))) →
      cValRank g a b p0 z y u0 ≤ r →
      ∃ z' : V → ℝ,
        z' ∈ DomR g ∧
        (∑ w : V, z' w ≤ ∑ w : V, z w) ∧
        SuppPosR z' y ⊆ SuppPosR z y ∧
        SuppNegR z' y ⊆ SuppNegR z y ∧
        (∀ v ∈ SuppNegR z' y, 0 ≤ Tp g a b p0 z' (fun w => (CharVec v w : ℝ))) ∧
        (suppPosFin z' y).card < (suppPosFin z y).card := by
  intro r
  induction r with
  | zero =>
    intro z hz hu0 h_v0 hr
    obtain ⟨zStar, hzS_dom, hzS_sum, hpos_sub, hneg_sub, hzS_v0, hstep⟩ :=
      slice_step_min g a b hrep hm p0 hz hy hu0 h_v0
    rcases hstep with hcard | ⟨_, hrank⟩
    · exact ⟨zStar, hzS_dom, hzS_sum, hpos_sub, hneg_sub, hzS_v0, hcard⟩
    · omega
  | succ r ih =>
    intro z hz hu0 h_v0 hr
    obtain ⟨zStar, hzS_dom, hzS_sum, hpos_sub, hneg_sub, hzS_v0, hstep⟩ :=
      slice_step_min g a b hrep hm p0 hz hy hu0 h_v0
    rcases hstep with hcard | ⟨hu0_S, hrank⟩
    · exact ⟨zStar, hzS_dom, hzS_sum, hpos_sub, hneg_sub, hzS_v0, hcard⟩
    · have hcard_le : (suppPosFin zStar y).card ≤ (suppPosFin z y).card := by
        apply Finset.card_le_card
        intro w hw
        exact mem_suppPosFin.mpr (hpos_sub (mem_suppPosFin.mp hw))
      obtain ⟨z', hz'_dom, hz'_sum, hpos_sub', hneg_sub', hz'_v0, hcard'⟩ :=
        ih zStar hzS_dom hu0_S hzS_v0 (by omega)
      exact ⟨z', hz'_dom, hz'_sum.trans hzS_sum, hpos_sub'.trans hpos_sub,
        hneg_sub'.trans hneg_sub, hz'_v0, hcard'.trans_le hcard_le⟩

lemma reduce_to_empty_pos (hrep : HasPolyRep g a b) (hm : MNatExchangeAxiomR g)
    (p0 : V → ℝ) (y : V → ℝ) (hy : y ∈ DomR g) :
    ∀ k : ℕ, ∀ z : V → ℝ,
      z ∈ DomR g →
      (∀ v ∈ SuppNegR z y, 0 ≤ Tp g a b p0 z (fun w => (CharVec v w : ℝ))) →
      (suppPosFin z y).card ≤ k →
      ∃ z' : V → ℝ,
        z' ∈ DomR g ∧
        (∑ w : V, z' w ≤ ∑ w : V, z w) ∧
        SuppNegR z' y ⊆ SuppNegR z y ∧
        (∀ v ∈ SuppNegR z' y, 0 ≤ Tp g a b p0 z' (fun w => (CharVec v w : ℝ))) ∧
        suppPosFin z' y = ∅ := by
  intro k
  induction k with
  | zero =>
    intro z hz h_v0 hk
    exact ⟨z, hz, le_rfl, Set.Subset.rfl, h_v0, Finset.card_eq_zero.mp ( Nat.le_zero.mp hk )⟩
  | succ k ih =>
    intro z hz h_v0 hk
    by_cases hne : (suppPosFin z y).Nonempty
    · obtain ⟨u0, hu0_fin⟩ := hne
      have hu0 : u0 ∈ SuppPosR z y := mem_suppPosFin.mp hu0_fin
      obtain ⟨z1, hz1_dom, hz1_sum, _, hneg_sub1, hz1_v0, hcard1⟩ :=
        slice_reduce_card g a b hrep hm p0 y hy u0 (cValRank g a b p0 z y u0) z hz hu0 h_v0 le_rfl
      obtain ⟨z', hz'_dom, hz'_sum, hneg_sub', hz'_v0, hempty⟩ :=
        ih z1 hz1_dom hz1_v0 (by omega)
      exact ⟨z', hz'_dom, hz'_sum.trans hz1_sum, hneg_sub'.trans hneg_sub1, hz'_v0, hempty⟩
    · exact ⟨z, hz, le_rfl, Set.Subset.rfl, h_v0, Finset.not_nonempty_iff_eq_empty.mp hne⟩

lemma sum_gt_exchange (hrep : HasPolyRep g a b) (hm : MNatExchangeAxiomR g)
    {x y : V → ℝ} (hx : x ∈ DomR g) (hy : y ∈ DomR g)
    (hsum : ∑ w : V, x w < ∑ w : V, y w) :
    ∃ v ∈ SuppNegR x y,
      T g a b x (fun w => (CharVec v w : ℝ)) + T g a b y (fun w => -(CharVec v w : ℝ)) ≤ 0 := by
  by_contra hno
  push_neg at hno
  let p0 : V → ℝ := fun v =>
    if T g a b x (fun w => (CharVec v w : ℝ)) = ⊤ then
      (T g a b y (fun w => -(CharVec v w : ℝ))).untopD 0 - 1
    else
      -((T g a b x (fun w => (CharVec v w : ℝ))).untopD 0)
  have hp0_x : ∀ v ∈ SuppNegR x y, 0 ≤ Tp g a b p0 x (fun w => (CharVec v w : ℝ)) := by
    intro v _
    dsimp [Tp]
    rw [sum_charVec_mul]
    by_cases htop : T g a b x (fun w => (CharVec v w : ℝ)) = ⊤
    · simp [htop]
    · obtain ⟨rx, hrx⟩ := WithTop.ne_top_iff_exists.mp htop
      have hp0_v : p0 v = -rx := by simp [p0, htop, ← hrx]
      rw [← hrx, hp0_v, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
      linarith
  have hp0_y : ∀ v ∈ SuppNegR x y, 0 < Tp g a b p0 y (fun w => -(CharVec v w : ℝ)) := by
    intro v hv
    dsimp [Tp]
    rw [sum_charVec_neg_mul]
    by_cases htop_x : T g a b x (fun w => (CharVec v w : ℝ)) = ⊤
    · by_cases htop_y : T g a b y (fun w => -(CharVec v w : ℝ)) = ⊤
      · simp [htop_y]
      · obtain ⟨ry, hry⟩ := WithTop.ne_top_iff_exists.mp htop_y
        have hp0_v : p0 v = ry - 1 := by simp [p0, htop_x, ← hry]
        rw [← hry, hp0_v, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_lt_coe]
        linarith
    · obtain ⟨rx, hrx⟩ := WithTop.ne_top_iff_exists.mp htop_x
      have hp0_v : p0 v = -rx := by simp [p0, htop_x, ← hrx]
      have hpos := hno v hv
      rw [← hrx] at hpos
      rw [hp0_v, neg_neg, add_comm]
      exact hpos
  obtain ⟨z', hz'_dom, hz'_sum, hneg_sub, hz'_v0, hempty⟩ :=
    reduce_to_empty_pos g a b hrep hm p0 y hy (suppPosFin x y).card x hx hp0_x le_rfl
  have hlt_sum : ∑ w : V, z' w < ∑ w : V, y w := lt_of_le_of_lt hz'_sum hsum
  have hex_neg : ∃ v : V, z' v < y v := by
    by_contra hall
    push_neg at hall
    have hge : ∑ w : V, y w ≤ ∑ w : V, z' w := Finset.sum_le_sum (fun w _ => hall w)
    linarith
  obtain ⟨v, hv_lt⟩ := hex_neg
  have hv_neg' : v ∈ SuppNegR z' y := hv_lt
  have hv_negx : v ∈ SuppNegR x y := hneg_sub hv_neg'
  have hv_pos_yz : v ∈ SuppPosR y z' := hv_lt
  rcases mnat_exc_T g a b hrep hm hy hz'_dom hv_pos_yz with hT1 | ⟨w0, hw0_neg, _⟩
  · rw [← Tp_add_neg g a b p0] at hT1
    have h1 := hz'_v0 v hv_neg'
    have h2 := hp0_y v hv_negx
    have hle0 : Tp g a b p0 y (fun w => -(CharVec v w : ℝ)) ≤ 0 :=
      withTop_le_zero_of_add_le_zero hT1 h1
    exact (not_lt_of_ge hle0) h2
  · have hw0_pos : w0 ∈ suppPosFin z' y := mem_suppPosFin.mpr hw0_neg
    rw [hempty] at hw0_pos
    exact (Finset.notMem_empty w0 hw0_pos).elim

lemma T_eq_coe_of_active_eq (hrep : HasPolyRep g a b) {p : V → ℝ} (hp : p ∈ DomR g)
    {d : V → ℝ} {c : ℝ}
    (heq : ∀ i ∈ ActiveSet g a b p, a i none * c + ∑ v : V, a i (some v) * d v = 0) :
    T g a b p d = (c : WithTop ℝ) := by
  have hle : T g a b p d ≤ (c : WithTop ℝ) :=
    (T_le_coe_iff g a b hrep hp d c).mpr (fun i hi => (heq i hi).le)
  have hne : T g a b p d ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
  obtain ⟨dr, hdr⟩ := WithTop.ne_top_iff_exists.mp hne
  have hdr_le : ∀ i ∈ ActiveSet g a b p, a i none * dr + ∑ v : V, a i (some v) * d v ≤ 0 :=
    (T_le_coe_iff g a b hrep hp d dr).mp hdr.symm.le
  obtain ⟨i0, hi0_act, hi0_neg⟩ := exists_neg_active g a b hrep hp
  have h1 := hdr_le i0 hi0_act
  have h2 := heq i0 hi0_act
  have hge : c ≤ dr := by nlinarith
  rw [← hdr, WithTop.coe_le_coe] at hle
  rw [← hdr, WithTop.coe_inj]
  linarith

lemma claim2_eq_sum (hrep : HasPolyRep g a b) (hm : MNatExchangeAxiomR g)
    {x y : V → ℝ} (hx : x ∈ DomR g) (hy : y ∈ DomR g)
    {u : V} (hu : u ∈ SuppPosR x y) (hsum_le : ∑ w : V, x w ≤ ∑ w : V, y w)
    (hT1 : T g a b x (fun w => -(CharVec u w : ℝ)) + T g a b y (fun w => (CharVec u w : ℝ)) ≤ 0) :
    ∃ v ∈ SuppNegR x y,
      T g a b x (fun w => -(CharVec u w : ℝ) + (CharVec v w : ℝ)) +
      T g a b y (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ)) ≤ 0 := by
  have hu_gt : y u < x u := hu
  have h0 : (0 : WithTop ℝ) ≠ ⊤ := WithTop.coe_ne_top
  obtain ⟨hTx_ne, hTy_ne⟩ := WithTop.add_ne_top.mp (ne_top_of_le_ne_top h0 hT1)
  obtain ⟨drx, hdrx⟩ := WithTop.ne_top_iff_exists.mp hTx_ne
  obtain ⟨dry, hdry⟩ := WithTop.ne_top_iff_exists.mp hTy_ne
  have hdrxy_le : drx + dry ≤ 0 := by
    rw [← hdrx, ← hdry, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at hT1
    exact hT1
  obtain ⟨εy, hεy, hray_y⟩ := ray_exact g a b hrep hy hdry.symm
  let δ := min εy (x u - y u) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hδ_ε : δ ≤ εy := by dsimp [δ]; linarith [min_le_left εy (x u - y u)]
  have hδ_u : δ < x u - y u := by dsimp [δ]; linarith [min_le_right εy (x u - y u)]
  let y1 : V → ℝ := fun w => y w + δ * (CharVec u w : ℝ)
  obtain ⟨hy1_g, hy1_act⟩ := hray_y δ hδ_pos hδ_ε
  have hy1_dom : y1 ∈ DomR g := by
    change g y1 ≠ ⊤; rw [hy1_g]; exact WithTop.coe_ne_top
  have hsum_y1 : ∑ w : V, x w < ∑ w : V, y1 w := by
    have hpt (w : V) : y1 w = y w + (if w = u then δ else 0) := by
      by_cases hwu : w = u
      · subst w; simp [y1, CharVec]
      · simp [y1, CharVec, hwu]
    simp_rw [hpt]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith
  obtain ⟨v, hv_neg1, hT_xy1⟩ := sum_gt_exchange g a b hrep hm hx hy1_dom hsum_y1
  have hv_lt1 : x v < y1 v := hv_neg1
  have hvu : v ≠ u := by
    intro h; subst v
    simp only [y1, CharVec, if_true, Int.cast_one, mul_one] at hv_lt1
    linarith
  have hv_neg : v ∈ SuppNegR x y := by
    change x v < y v
    simpa [y1, CharVec, hvu] using hv_lt1
  obtain ⟨hTxv_ne, hTy1v_ne⟩ := WithTop.add_ne_top.mp (ne_top_of_le_ne_top h0 hT_xy1)
  obtain ⟨drxv, hdrxv⟩ := WithTop.ne_top_iff_exists.mp hTxv_ne
  obtain ⟨drv, hdrv⟩ := WithTop.ne_top_iff_exists.mp hTy1v_ne
  have hdrxvv_le : drxv + drv ≤ 0 := by
    rw [← hdrxv, ← hdrv, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at hT_xy1
    exact hT_xy1
  obtain ⟨ε1, hε1, hray_y1⟩ := ray_exact g a b hrep hy1_dom hdrv.symm
  let α := min ε1 δ / 2
  have hα_pos : 0 < α := by dsimp [α]; positivity
  have hα_ε : α ≤ ε1 := by dsimp [α]; linarith [min_le_left ε1 δ]
  let p : V → ℝ := fun w => y1 w + α * -(CharVec v w : ℝ)
  obtain ⟨hp_g, hp_act⟩ := hray_y1 α hα_pos hα_ε
  have hp_dom : p ∈ DomR g := by
    change g p ≠ ⊤; rw [hp_g]; exact WithTop.coe_ne_top
  have hp_act_prop : ∀ i ∈ ActiveSet g a b p,
      a i none * dry + a i (some u) = 0 ∧ a i none * drv - a i (some v) = 0 := by
    intro i hi
    change i ∈ ActiveSet g a b (fun w => y1 w + α * -(CharVec v w : ℝ)) at hi
    rw [hp_act, Finset.mem_filter] at hi
    obtain ⟨hi_y1, hi_eq_v⟩ := hi
    change i ∈ ActiveSet g a b (fun w => y w + δ * (CharVec u w : ℝ)) at hi_y1
    rw [hy1_act, Finset.mem_filter] at hi_y1
    obtain ⟨_, hi_eq_u⟩ := hi_y1
    rw [sum_charVec_mul] at hi_eq_u
    rw [sum_charVec_neg_mul] at hi_eq_v
    exact ⟨hi_eq_u, by linarith⟩
  have hTp_v : T g a b p (fun w => (CharVec v w : ℝ)) = ((-drv : ℝ) : WithTop ℝ) := by
    apply T_eq_coe_of_active_eq g a b hrep hp_dom
    intro i hi
    have h := (hp_act_prop i hi).2
    rw [sum_charVec_mul]
    linarith
  have hTp_uv : T g a b p (fun w => (CharVec v w : ℝ) - (CharVec u w : ℝ)) =
      (((-dry - drv : ℝ)) : WithTop ℝ) := by
    apply T_eq_coe_of_active_eq g a b hrep hp_dom
    intro i hi
    obtain ⟨hu_eq, hv_eq⟩ := hp_act_prop i hi
    have hsum : (∑ w : V, a i (some w) * ((CharVec v w : ℝ) - (CharVec u w : ℝ))) =
        a i (some v) - a i (some u) := by
      have hpt (w : V) : a i (some w) * ((CharVec v w : ℝ) - (CharVec u w : ℝ)) =
          a i (some w) * (CharVec v w : ℝ) - a i (some w) * (CharVec u w : ℝ) := by ring
      simp_rw [hpt]
      rw [Finset.sum_sub_distrib, sum_charVec_mul, sum_charVec_mul]
    rw [hsum]
    linarith
  have hv_pos_yp : v ∈ SuppPosR y p := by
    change p v < y v
    simp only [p, y1, CharVec, if_true, if_neg hvu, Int.cast_one, Int.cast_zero, mul_zero, add_zero, mul_neg, mul_one]
    linarith
  have hneg_yp : ∀ w ∈ SuppNegR y p, w = u := by
    intro w hw
    change y w < p w at hw
    by_contra hwu
    by_cases hwv : w = v
    · subst w
      simp only [p, y1, CharVec, if_true, if_neg hvu, Int.cast_one, Int.cast_zero, mul_zero, add_zero, mul_neg, mul_one] at hw
      linarith
    · simp only [p, y1, CharVec, if_neg hwu, if_neg hwv, Int.cast_zero, mul_zero, add_zero, neg_zero] at hw
      linarith
  have hTy_uv_le : T g a b y (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ)) ≤
      (((dry + drv : ℝ)) : WithTop ℝ) := by
    rcases mnat_exc_T g a b hrep hm hy hp_dom hv_pos_yp with hTy1 | ⟨w0, hw0_neg, hTy2⟩
    · rw [hTp_v] at hTy1
      have hTy_v_le : T g a b y (fun w => -(CharVec v w : ℝ)) ≤ (drv : WithTop ℝ) := by
        cases h : T g a b y (fun w => -(CharVec v w : ℝ)) with
        | top => simp [h] at hTy1
        | coe r =>
          rw [h, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at hTy1
          rw [WithTop.coe_le_coe]; linarith
      have heq_d : (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ)) =
          (fun w => (CharVec u w : ℝ) + -(CharVec v w : ℝ)) := by funext w; ring
      rw [heq_d]
      refine (T_subadd g a b hrep hy (fun w => (CharVec u w : ℝ)) (fun w => -(CharVec v w : ℝ))).trans ?_
      rw [← hdry, WithTop.coe_add]
      exact add_le_add le_rfl hTy_v_le
    · have hw0_eq : w0 = u := hneg_yp w0 hw0_neg
      subst w0
      have heq_y : (fun w => -(CharVec v w : ℝ) + (CharVec u w : ℝ)) =
          (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ)) := by funext w; ring
      rw [heq_y, hTp_uv] at hTy2
      cases h : T g a b y (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ)) with
      | top => simp [h] at hTy2
      | coe r =>
        rw [h, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at hTy2
        rw [WithTop.coe_le_coe]; linarith
  have hTx_uv_le : T g a b x (fun w => -(CharVec u w : ℝ) + (CharVec v w : ℝ)) ≤
      (((drx + drxv : ℝ)) : WithTop ℝ) := by
    refine (T_subadd g a b hrep hx (fun w => -(CharVec u w : ℝ)) (fun w => (CharVec v w : ℝ))).trans ?_
    rw [← hdrx, ← hdrxv, ← WithTop.coe_add]
  refine ⟨v, hv_neg, ?_⟩
  refine (add_le_add hTx_uv_le hTy_uv_le).trans ?_
  rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
  linarith

end PolyTangent

def liftVecR (x : V → ℝ) : Option V → ℝ :=
  fun w => w.elim (-(∑ v : V, x v)) x

@[simp] lemma liftVecR_none (x : V → ℝ) :
    liftVecR x none = -(∑ v : V, x v) := rfl

@[simp] lemma liftVecR_some (x : V → ℝ) (v : V) :
    liftVecR x (some v) = x v := rfl

lemma liftedFunctionR_liftVecR (g : (V → ℝ) → WithTop ℝ) (x : V → ℝ) :
    LiftedFunctionR g (liftVecR x) = g x := by
  simp [LiftedFunctionR]

lemma eq_liftVecR_of_mem_domR {g : (V → ℝ) → WithTop ℝ} {xt : Option V → ℝ}
    (hxt : xt ∈ DomR (LiftedFunctionR g)) :
    xt = liftVecR (fun v => xt (some v)) ∧ (fun v => xt (some v)) ∈ DomR g := by
  dsimp [DomR, LiftedFunctionR] at hxt
  split_ifs at hxt with hsum
  · refine ⟨?_, hxt⟩
    ext w
    cases w with
    | none => exact hsum
    | some v => rfl
  · exact absurd rfl hxt

lemma sum_charVecR (u : V) : (∑ v : V, (CharVec u v : ℝ)) = 1 := by
  have hpt (v : V) : (CharVec u v : ℝ) = if v = u then 1 else 0 := by
    dsimp [CharVec]; split_ifs <;> norm_num
  simp_rw [hpt]
  simp

lemma charVec_some_none (u : V) : (CharVec (some u) (none : Option V) : ℝ) = 0 := by
  simp [CharVec]

lemma charVec_none_none : (CharVec (none : Option V) (none : Option V) : ℝ) = 1 := by
  simp [CharVec]

lemma liftVecR_sub_some_none (x : V → ℝ) (u : V) (α : ℝ) :
    (fun w => liftVecR x w - α * ((CharVec (some u) w : ℝ) - (CharVec (none : Option V) w : ℝ))) =
    liftVecR (fun v => x v - α * (CharVec u v : ℝ)) := by
  ext w
  cases w with
  | none =>
    simp only [liftVecR_none, charVec_some_none, charVec_none_none,
      Finset.sum_sub_distrib, ← Finset.mul_sum, sum_charVecR]
    ring
  | some v =>
    have h1 : (CharVec (some u) (some v) : ℝ) = (CharVec u v : ℝ) := by simp [CharVec]
    have h2 : (CharVec (none : Option V) (some v) : ℝ) = 0 := by simp [CharVec]
    simp only [liftVecR_some, h1, h2, sub_zero]

lemma liftVecR_add_some_none (y : V → ℝ) (u : V) (α : ℝ) :
    (fun w => liftVecR y w + α * ((CharVec (some u) w : ℝ) - (CharVec (none : Option V) w : ℝ))) =
    liftVecR (fun v => y v + α * (CharVec u v : ℝ)) := by
  ext w
  cases w with
  | none =>
    simp only [liftVecR_none, charVec_some_none, charVec_none_none,
      Finset.sum_add_distrib, ← Finset.mul_sum, sum_charVecR]
    ring
  | some v =>
    have h1 : (CharVec (some u) (some v) : ℝ) = (CharVec u v : ℝ) := by simp [CharVec]
    have h2 : (CharVec (none : Option V) (some v) : ℝ) = 0 := by simp [CharVec]
    simp only [liftVecR_some, h1, h2, sub_zero]

lemma liftVecR_sub_none_some (x : V → ℝ) (v : V) (α : ℝ) :
    (fun w => liftVecR x w - α * ((CharVec (none : Option V) w : ℝ) - (CharVec (some v) w : ℝ))) =
    liftVecR (fun w => x w - α * -(CharVec v w : ℝ)) := by
  ext w
  cases w with
  | none =>
    have hsum : (∑ w : V, α * -(CharVec v w : ℝ)) = -α := by
      have hpt (w : V) : α * -(CharVec v w : ℝ) = -(α * (CharVec v w : ℝ)) := by ring
      simp_rw [hpt]
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum, sum_charVecR]
      ring
    simp only [liftVecR_none, charVec_some_none, charVec_none_none,
      Finset.sum_sub_distrib, hsum]
    ring
  | some u =>
    have h1 : (CharVec (some v) (some u) : ℝ) = (CharVec v u : ℝ) := by simp [CharVec]
    have h2 : (CharVec (none : Option V) (some u) : ℝ) = 0 := by simp [CharVec]
    simp only [liftVecR_some, h1, h2, zero_sub]

lemma liftVecR_add_none_some (y : V → ℝ) (v : V) (α : ℝ) :
    (fun w => liftVecR y w + α * ((CharVec (none : Option V) w : ℝ) - (CharVec (some v) w : ℝ))) =
    liftVecR (fun w => y w + α * -(CharVec v w : ℝ)) := by
  ext w
  cases w with
  | none =>
    have hsum : (∑ w : V, α * -(CharVec v w : ℝ)) = -α := by
      have hpt (w : V) : α * -(CharVec v w : ℝ) = -(α * (CharVec v w : ℝ)) := by ring
      simp_rw [hpt]
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum, sum_charVecR]
      ring
    simp only [liftVecR_none, charVec_some_none, charVec_none_none,
      Finset.sum_add_distrib, hsum]
    ring
  | some u =>
    have h1 : (CharVec (some v) (some u) : ℝ) = (CharVec v u : ℝ) := by simp [CharVec]
    have h2 : (CharVec (none : Option V) (some u) : ℝ) = 0 := by simp [CharVec]
    simp only [liftVecR_some, h1, h2, zero_sub]

lemma liftVecR_sub_some_some (x : V → ℝ) (u v : V) (α : ℝ) :
    (fun w => liftVecR x w - α * ((CharVec (some u) w : ℝ) - (CharVec (some v) w : ℝ))) =
    liftVecR (fun w => x w - α * ((CharVec u w : ℝ) - (CharVec v w : ℝ))) := by
  ext w
  cases w with
  | none =>
    have hsum : (∑ w : V, α * ((CharVec u w : ℝ) - (CharVec v w : ℝ))) = 0 := by
      have hpt (w : V) : α * ((CharVec u w : ℝ) - (CharVec v w : ℝ)) =
          α * (CharVec u w : ℝ) - α * (CharVec v w : ℝ) := by ring
      simp_rw [hpt]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_charVecR, sum_charVecR]
      ring
    simp only [liftVecR_none, charVec_some_none,
      Finset.sum_sub_distrib, hsum]
    ring
  | some w0 =>
    have h1 : (CharVec (some u) (some w0) : ℝ) = (CharVec u w0 : ℝ) := by simp [CharVec]
    have h2 : (CharVec (some v) (some w0) : ℝ) = (CharVec v w0 : ℝ) := by simp [CharVec]
    simp only [liftVecR_some, h1, h2]

lemma liftVecR_add_some_some (y : V → ℝ) (u v : V) (α : ℝ) :
    (fun w => liftVecR y w + α * ((CharVec (some u) w : ℝ) - (CharVec (some v) w : ℝ))) =
    liftVecR (fun w => y w + α * ((CharVec u w : ℝ) - (CharVec v w : ℝ))) := by
  ext w
  cases w with
  | none =>
    have hsum : (∑ w : V, α * ((CharVec u w : ℝ) - (CharVec v w : ℝ))) = 0 := by
      have hpt (w : V) : α * ((CharVec u w : ℝ) - (CharVec v w : ℝ)) =
          α * (CharVec u w : ℝ) - α * (CharVec v w : ℝ) := by ring
      simp_rw [hpt]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_charVecR, sum_charVecR]
      ring
    simp only [liftVecR_none, charVec_some_none,
      Finset.sum_add_distrib, hsum]
    ring
  | some w0 =>
    have h1 : (CharVec (some u) (some w0) : ℝ) = (CharVec u w0 : ℝ) := by simp [CharVec]
    have h2 : (CharVec (some v) (some w0) : ℝ) = (CharVec v w0 : ℝ) := by simp [CharVec]
    simp only [liftVecR_some, h1, h2]

end PolyMNatEquiv

open PolyMNatEquiv

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℝ) → WithTop ℝ) (hdom : (DomR g).Nonempty)
    (hpoly : IsPolyhedralConvex g) : MNaturalConvexR g ↔ MNatExchangeAxiomR g := by
  let _ := hdom
  constructor
  · intro hM x hx y hy u hu
    have hxL : liftVecR x ∈ DomR (LiftedFunctionR g) := by
      simpa [DomR, liftedFunctionR_liftVecR] using hx
    have hyL : liftVecR y ∈ DomR (LiftedFunctionR g) := by
      simpa [DomR, liftedFunctionR_liftVecR] using hy
    have huL : some u ∈ SuppPosR (liftVecR x) (liftVecR y) := hu
    obtain ⟨vt, hvt, α0, hα0, hstep⟩ := hM (liftVecR x) hxL (liftVecR y) hyL (some u) huL
    cases vt with
    | none =>
      refine ⟨none, Or.inl rfl, α0, hα0, fun α hα0 hαm => ?_⟩
      have h := hstep α hα0 hαm
      rw [liftedFunctionR_liftVecR, liftedFunctionR_liftVecR,
          liftVecR_sub_some_none, liftVecR_add_some_none,
          liftedFunctionR_liftVecR, liftedFunctionR_liftVecR] at h
      simpa [CharVecOptR] using h
    | some v =>
      have hv : v ∈ SuppNegR x y := hvt
      refine ⟨some v, Or.inr ⟨v, rfl, hv⟩, α0, hα0, fun α hα0 hαm => ?_⟩
      have h := hstep α hα0 hαm
      rw [liftedFunctionR_liftVecR, liftedFunctionR_liftVecR,
          liftVecR_sub_some_some, liftVecR_add_some_some,
          liftedFunctionR_liftVecR, liftedFunctionR_liftVecR] at h
      simpa [CharVecOptR] using h
  · intro hm xt hxt yt hyt ut hut
    obtain ⟨m, a, b, hrep⟩ := exists_poly_rep g hpoly
    let x : V → ℝ := fun v => xt (some v)
    let y : V → ℝ := fun v => yt (some v)
    obtain ⟨hxt_eq, hx⟩ := eq_liftVecR_of_mem_domR hxt
    obtain ⟨hyt_eq, hy⟩ := eq_liftVecR_of_mem_domR hyt
    rw [hxt_eq, hyt_eq] at hut ⊢
    cases ut with
    | none =>
      have hsum : ∑ v : V, x v < ∑ v : V, y v := by
        change liftVecR y none < liftVecR x none at hut
        simp only [liftVecR_none] at hut
        linarith
      obtain ⟨v, hv, hT⟩ := sum_gt_exchange g a b hrep hm hx hy hsum
      have heq_neg : (fun w => - -(CharVec v w : ℝ)) = (fun w => (CharVec v w : ℝ)) := by
        funext w; ring
      rw [← heq_neg] at hT
      obtain ⟨α0, hα0, hstep⟩ := (step_iff_T_add_nonpos g a b hrep hx hy (fun w => -(CharVec v w : ℝ))).mpr hT
      refine ⟨some v, hv, α0, hα0, fun α hα0 hαm => ?_⟩
      rw [liftedFunctionR_liftVecR, liftedFunctionR_liftVecR,
          liftVecR_sub_none_some, liftVecR_add_none_some,
          liftedFunctionR_liftVecR, liftedFunctionR_liftVecR]
      exact hstep α hα0 hαm
    | some u =>
      have hu : u ∈ SuppPosR x y := hut
      rcases mnat_exc_T g a b hrep hm hx hy hu with hT1 | ⟨v, hv, hT2⟩
      · by_cases hsum_lt : ∑ v : V, y v < ∑ v : V, x v
        · obtain ⟨α0, hα0, hstep⟩ := (step_iff_T_add_nonpos g a b hrep hx hy (fun w => (CharVec u w : ℝ))).mpr hT1
          have hnone_neg : (none : Option V) ∈ SuppNegR (liftVecR x) (liftVecR y) := by
            change liftVecR x none < liftVecR y none
            simp only [liftVecR_none]
            linarith
          refine ⟨none, hnone_neg, α0, hα0, fun α hα0 hαm => ?_⟩
          rw [liftedFunctionR_liftVecR, liftedFunctionR_liftVecR,
              liftVecR_sub_some_none, liftVecR_add_some_none,
              liftedFunctionR_liftVecR, liftedFunctionR_liftVecR]
          exact hstep α hα0 hαm
        · obtain ⟨v, hv, hT2⟩ := claim2_eq_sum g a b hrep hm hx hy hu (by linarith) hT1
          have heq : (fun w => -(CharVec u w : ℝ) + (CharVec v w : ℝ)) =
              (fun w => -((CharVec u w : ℝ) - (CharVec v w : ℝ))) := by funext w; ring
          rw [heq] at hT2
          obtain ⟨α0, hα0, hstep⟩ := (step_iff_T_add_nonpos g a b hrep hx hy
            (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ))).mpr hT2
          refine ⟨some v, hv, α0, hα0, fun α hα0 hαm => ?_⟩
          rw [liftedFunctionR_liftVecR, liftedFunctionR_liftVecR,
              liftVecR_sub_some_some, liftVecR_add_some_some,
              liftedFunctionR_liftVecR, liftedFunctionR_liftVecR]
          exact hstep α hα0 hαm
      · have heq : (fun w => -(CharVec u w : ℝ) + (CharVec v w : ℝ)) =
            (fun w => -((CharVec u w : ℝ) - (CharVec v w : ℝ))) := by funext w; ring
        rw [heq] at hT2
        obtain ⟨α0, hα0, hstep⟩ := (step_iff_T_add_nonpos g a b hrep hx hy
          (fun w => (CharVec u w : ℝ) - (CharVec v w : ℝ))).mpr hT2
        refine ⟨some v, hv, α0, hα0, fun α hα0 hαm => ?_⟩
        rw [liftedFunctionR_liftVecR, liftedFunctionR_liftVecR,
            liftVecR_sub_some_some, liftVecR_add_some_some,
            liftedFunctionR_liftVecR, liftedFunctionR_liftVecR]
        exact hstep α hα0 hαm
