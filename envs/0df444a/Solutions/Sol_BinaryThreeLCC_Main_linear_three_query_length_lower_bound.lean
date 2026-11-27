-- Prove2me | solution 1 for BinaryThreeLCC.Main.linear_three_query_length_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:06:03.812843+00:00
-- url     : https://prove2.me/submissions/010844dd-ad6d-45aa-9ef0-5b7ccb14e9c7

import Definitions.Def_BinaryThreeLCC_Main_Matchings
import Theorems.Thm_BinaryThreeLCC_JM_padded_span_dimension
import Theorems.Thm_BinaryThreeLCC_JM_recovery_matching_of_corrects
import Theorems.Thm_BinaryThreeLCC_JM_eulerian_cut_dense_piece
import Theorems.Thm_BinaryThreeLCC_JM_dimension_bound

set_option autoImplicit false

namespace BinaryThreeLCC.JM

open BinaryThreeLCC.Main

namespace MainAux

open Finset

theorem finrank_sup_le_quot {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    [FiniteDimensional K X] (U0 T : Submodule K X) :
    Module.finrank K ↥(U0 ⊔ T) ≤
      Module.finrank K ↥U0 + Module.finrank K ↥(T.map U0.mkQ) := by
  set P := U0 ⊔ T
  let g : ↥P →ₗ[K] X ⧸ U0 := U0.mkQ.comp P.subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have hr : LinearMap.range g ≤ T.map U0.mkQ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 x.2
    refine ⟨z, hz, ?_⟩
    have : U0.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero U0).2 hy
    simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, ← hyz, map_add, this, zero_add]
  have hk : Module.finrank K ↥(LinearMap.ker g) ≤ Module.finrank K ↥U0 := by
    have hle : (LinearMap.ker g).map P.subtype ≤ U0 := by
      rintro _ ⟨x, hx, rfl⟩
      simpa [g] using hx
    calc Module.finrank K ↥(LinearMap.ker g)
        = Module.finrank K ↥((LinearMap.ker g).map P.subtype) :=
          (Submodule.finrank_map_subtype_eq _ _).symm
      _ ≤ _ := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_mono hr
  omega

open Classical in
/-- Abstract iteration: repeatedly absorbing at least `s` new indices costs at most `B`. -/
theorem iterate_bound {K X ι : Type*} [Field K] [AddCommGroup X] [Module K X]
    [FiniteDimensional K X] [Fintype ι] (v : ι → X) (s B : ℝ) (hs : 0 < s) (hB : 0 ≤ B)
    (step : ∀ U0 : Submodule K X, (univ.filter (fun i => v i ∉ U0)).Nonempty →
      ∃ U1 : Submodule K X, U0 ≤ U1 ∧ U1 ≤ U0 ⊔ Submodule.span K (Set.range v) ∧
        (Module.finrank K ↥U1 : ℝ) ≤ Module.finrank K ↥U0 + B ∧
        ((univ.filter (fun i => v i ∉ U1)).card : ℝ) + s ≤
          (univ.filter (fun i => v i ∉ U0)).card) :
    (Module.finrank K ↥(Submodule.span K (Set.range v)) : ℝ) ≤
      (Fintype.card ι : ℝ) / s * B := by
  classical
  set S := Submodule.span K (Set.range v)
  have key : ∀ m : ℕ, ∀ U0 : Submodule K X, (univ.filter (fun i => v i ∉ U0)).card = m →
      (Module.finrank K ↥(U0 ⊔ S) : ℝ) ≤ Module.finrank K ↥U0 + m / s * B := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro U0 hm
      by_cases hne : (univ.filter (fun i => v i ∉ U0)).Nonempty
      · obtain ⟨U1, h01, h1S, hfr, hcnt⟩ := step U0 hne
        have hlt : (univ.filter (fun i => v i ∉ U1)).card < m := by
          have : ((univ.filter (fun i => v i ∉ U1)).card : ℝ) < m := by
            rw [← hm]; linarith
          exact_mod_cast this
        have h := ih _ hlt U1 rfl
        have hsup : U1 ⊔ S = U0 ⊔ S := by
          apply le_antisymm
          · exact sup_le h1S le_sup_right
          · exact sup_le (le_trans h01 le_sup_left) le_sup_right
        rw [hsup] at h
        have hc : ((univ.filter (fun i => v i ∉ U1)).card : ℝ) ≤ m - s := by
          rw [← hm]; linarith
        have : ((univ.filter (fun i => v i ∉ U1)).card : ℝ) / s * B ≤ (m - s) / s * B := by
          apply mul_le_mul_of_nonneg_right _ hB
          exact div_le_div_of_nonneg_right hc hs.le
        have h3 : (m - s) / s * B = m / s * B - B := by field_simp
        linarith
      · have hS : S ≤ U0 := by
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          by_contra hi
          exact hne ⟨i, by simpa using hi⟩
        rw [sup_eq_left.2 hS]
        have : (0 : ℝ) ≤ m / s * B := by positivity
        linarith
  have h := key _ ⊥ rfl
  rw [bot_sup_eq] at h
  simp only [finrank_bot, Nat.cast_zero, zero_add] at h
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_right _ hB
  apply div_le_div_of_nonneg_right _ hs.le
  exact_mod_cast (card_le_univ _)

end MainAux

namespace MainAux

open Finset

section TS
set_option linter.unusedSectionVars false

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Hypotheses on recovery hyperedges with chosen targets and an arc set. -/
structure TSHyp (U : Finset α) (H : α → Finset (Finset α)) (t : α → Finset α → α)
    (F : Finset (α × α)) : Prop where
  card3 : ∀ u ∈ U, ∀ e ∈ H u, e.card = 3
  tmem : ∀ u ∈ U, ∀ e ∈ H u, t u e ∈ e
  disj : ∀ u ∈ U, ∀ e ∈ H u, ∀ e' ∈ H u, e ≠ e' → Disjoint e e'
  hF : ∀ p ∈ F, p.1 ∈ U ∧ p.2 ∈ U ∧ ∃ e ∈ H p.1, t p.1 e = p.2

variable {U : Finset α} {H : α → Finset (Finset α)} {t : α → Finset α → α} {F : Finset (α × α)}

def IsRealT (H : α → Finset (Finset α)) (t : α → Finset α → α) (F : Finset (α × α))
    (u a : α) : Prop :=
  ∃ e ∈ H u, a ∈ e ∧ a ≠ t u e ∧ (u, t u e) ∈ F

open Classical in
noncomputable def edgeOf (H : α → Finset (Finset α)) (t : α → Finset α → α)
    (F : Finset (α × α)) (u a : α) : Finset α :=
  if h : IsRealT H t F u a then h.choose else ∅

noncomputable def partnerOf (H : α → Finset (Finset α)) (t : α → Finset α → α)
    (F : Finset (α × α)) (u a : α) : α :=
  (((edgeOf H t F u a).erase a).erase (t u (edgeOf H t F u a))).toList.headD a

theorem edgeOf_spec {u a : α} (h : IsRealT H t F u a) :
    edgeOf H t F u a ∈ H u ∧ a ∈ edgeOf H t F u a ∧ a ≠ t u (edgeOf H t F u a) ∧
      (u, t u (edgeOf H t F u a)) ∈ F := by
  classical
  unfold edgeOf
  rw [dif_pos h]
  exact h.choose_spec

theorem t_inj (hyp : TSHyp U H t F) {u : α} (hu : u ∈ U) {e e' : Finset α} (he : e ∈ H u)
    (he' : e' ∈ H u) (h : t u e = t u e') : e = e' := by
  by_contra hne
  have hd := hyp.disj u hu e he e' he' hne
  exact Finset.disjoint_left.1 hd (hyp.tmem u hu e he) (h ▸ hyp.tmem u hu e' he')

theorem edge_uniq (hyp : TSHyp U H t F) {u : α} (hu : u ∈ U) {e e' : Finset α} (he : e ∈ H u)
    (he' : e' ∈ H u) {a : α} (ha : a ∈ e) (ha' : a ∈ e') : e = e' := by
  by_contra hne
  exact Finset.disjoint_left.1 (hyp.disj u hu e he e' he' hne) ha ha'

theorem real_iff (hyp : TSHyp U H t F) {u : α} (hu : u ∈ U) {e : Finset α} (he : e ∈ H u)
    {a : α} (ha : a ∈ e) : IsRealT H t F u a ↔ a ≠ t u e ∧ (u, t u e) ∈ F := by
  constructor
  · rintro ⟨e', he', ha', h1, h2⟩
    have := edge_uniq hyp hu he he' ha ha'
    subst this
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e, he, ha, h1, h2⟩

theorem edgeOf_eq (hyp : TSHyp U H t F) {u : α} (hu : u ∈ U) {e : Finset α} (he : e ∈ H u)
    {a : α} (ha : a ∈ e) (hr : IsRealT H t F u a) : edgeOf H t F u a = e := by
  obtain ⟨h1, h2, -, -⟩ := edgeOf_spec hr
  exact edge_uniq hyp hu h1 he h2 ha

theorem three_eq (hyp : TSHyp U H t F) {u : α} (hu : u ∈ U) {a : α}
    (hr : IsRealT H t F u a) :
    ((edgeOf H t F u a).erase a).erase (t u (edgeOf H t F u a)) = {partnerOf H t F u a} := by
  obtain ⟨h1, h2, h3, -⟩ := edgeOf_spec hr
  set e := edgeOf H t F u a
  have hc : (((e.erase a).erase (t u e))).card = 1 := by
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem h2, hyp.card3 u hu e h1]
    exact Finset.mem_erase.2 ⟨fun h => h3 h.symm, hyp.tmem u hu e h1⟩
  obtain ⟨b, hb⟩ := Finset.card_eq_one.1 hc
  have : partnerOf H t F u a = b := by
    unfold partnerOf
    rw [hb, Finset.toList_singleton]
    rfl
  rw [hb, this]

theorem partner_mem (hyp : TSHyp U H t F) {u : α} (hu : u ∈ U) {a : α}
    (hr : IsRealT H t F u a) :
    partnerOf H t F u a ∈ edgeOf H t F u a ∧ partnerOf H t F u a ≠ a ∧
      partnerOf H t F u a ≠ t u (edgeOf H t F u a) := by
  have h := three_eq hyp hu hr
  have hm : partnerOf H t F u a ∈ ((edgeOf H t F u a).erase a).erase
      (t u (edgeOf H t F u a)) := by rw [h]; exact Finset.mem_singleton_self _
  simp only [Finset.mem_erase] at hm
  exact ⟨hm.2.2, hm.2.1, hm.1⟩

theorem partner_not_real {u a : α} (hr : ¬ IsRealT H t F u a) : partnerOf H t F u a = a := by
  classical
  unfold partnerOf edgeOf
  rw [dif_neg hr]
  simp

theorem partner_real (hyp : TSHyp U H t F) {u : α} (hu : u ∈ U) {a : α}
    (hr : IsRealT H t F u a) :
    IsRealT H t F u (partnerOf H t F u a) ∧
      edgeOf H t F u (partnerOf H t F u a) = edgeOf H t F u a := by
  obtain ⟨h1, h2, h3, h4⟩ := edgeOf_spec hr
  obtain ⟨p1, p2, p3⟩ := partner_mem hyp hu hr
  have hpr : IsRealT H t F u (partnerOf H t F u a) := (real_iff hyp hu h1 p1).2 ⟨p3, h4⟩
  exact ⟨hpr, edgeOf_eq hyp hu h1 p1 hpr⟩

theorem partner_invol (hyp : TSHyp U H t F) {u : α} (hu : u ∈ U) (a : α) :
    partnerOf H t F u (partnerOf H t F u a) = a := by
  by_cases hr : IsRealT H t F u a
  · obtain ⟨hpr, hpe⟩ := partner_real hyp hu hr
    obtain ⟨h1, h2, h3, h4⟩ := edgeOf_spec hr
    obtain ⟨p1, p2, p3⟩ := partner_mem hyp hu hr
    have h := three_eq hyp hu hpr
    rw [hpe] at h
    have ha : a ∈ ((edgeOf H t F u a).erase (partnerOf H t F u a)).erase
        (t u (edgeOf H t F u a)) := by
      simp only [Finset.mem_erase]
      exact ⟨h3, p2.symm, h2⟩
    rw [h] at ha
    exact (Finset.mem_singleton.1 ha).symm
  · rw [partner_not_real hr, partner_not_real hr]

theorem sum_edge {W : Type*} [AddCommGroup W] (hyp : TSHyp U H t F) {u : α} (hu : u ∈ U)
    {a : α} (hr : IsRealT H t F u a) (v : α → W) :
    ∑ x ∈ edgeOf H t F u a, v x =
      v a + v (partnerOf H t F u a) + v (t u (edgeOf H t F u a)) := by
  obtain ⟨h1, h2, h3, h4⟩ := edgeOf_spec hr
  have h := three_eq hyp hu hr
  set e := edgeOf H t F u a
  have ht : t u e ∈ e.erase a := Finset.mem_erase.2 ⟨fun h => h3 h.symm, hyp.tmem u hu e h1⟩
  rw [← Finset.add_sum_erase _ _ h2, ← Finset.add_sum_erase _ _ ht, h, Finset.sum_singleton]
  abel

open Classical in
/-- Fibre counting: real pairs ↔ two per arc. -/
theorem count_real (hyp : TSHyp U H t F) (P : α → α → Prop) :
    (Finset.univ.filter (fun q : ↥U × α => IsRealT H t F q.1 q.2 ∧
        P q.1 (t q.1 (edgeOf H t F q.1 q.2)))).card =
      2 * (F.filter (fun p => P p.1 p.2)).card := by
  set A := Finset.univ.filter (fun q : ↥U × α => IsRealT H t F q.1 q.2 ∧
        P q.1 (t q.1 (edgeOf H t F q.1 q.2)))
  let f : ↥U × α → α × α := fun q => ((q.1 : α), t q.1 (edgeOf H t F q.1 q.2))
  have hmaps : (A : Set (↥U × α)).MapsTo f (F.filter (fun p => P p.1 p.2)) := by
    intro q hq
    simp only [A, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, f]
    exact ⟨(edgeOf_spec hq.1).2.2.2, hq.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps, mul_comm, ← smul_eq_mul,
    ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_filter] at hp
  obtain ⟨hp1, hp2, e, he, hte⟩ := hyp.hF p hp.1
  have hcard : (e.erase p.2).card = 2 := by
    rw [Finset.card_erase_of_mem (hte ▸ hyp.tmem _ hp1 e he), hyp.card3 _ hp1 e he]
  rw [← hcard]
  let g : α → ↥U × α := fun a => (⟨p.1, hp1⟩, a)
  have hg : Function.Injective g := fun a b h => by simpa [g] using h
  rw [← Finset.card_image_of_injective _ hg]
  congr 1
  ext q
  simp only [Finset.mem_filter, A, Finset.mem_univ, true_and, Finset.mem_image, f, g]
  constructor
  · rintro ⟨⟨hr, -⟩, hq⟩
    rw [Prod.ext_iff] at hq
    obtain ⟨hq1, hq2⟩ := hq
    obtain ⟨h1, h2, h3, h4⟩ := edgeOf_spec hr
    have hu : (q.1 : α) ∈ U := q.1.2
    have hq1' : (q.1 : α) = p.1 := hq1
    rw [hq1'] at h1 hq2
    have hee : edgeOf H t F q.1 q.2 = e := by
      rw [hq1'] at h2 h3 ⊢
      exact t_inj hyp hp1 h1 he (hq2.trans hte.symm)
    refine ⟨q.2, Finset.mem_erase.2 ⟨?_, hee ▸ h2⟩, ?_⟩
    · intro h; apply h3; rw [hee, h]; simp [hq1', hte]
    · ext
      · simp [hq1']
      · rfl
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ha1, ha2⟩ := Finset.mem_erase.1 ha
    have hr : IsRealT H t F p.1 a := (real_iff hyp hp1 he ha2).2 ⟨hte ▸ ha1, by
      rw [hte]; exact hp.1⟩
    have hee := edgeOf_eq hyp hp1 he ha2 hr
    refine ⟨⟨hr, ?_⟩, ?_⟩
    · simp only [hee, hte]; exact hp.2
    · simp [hee, hte]

end TS

end MainAux

namespace MainAux

open Finset

section TS2
set_option linter.unusedSectionVars false

variable {α : Type} [Fintype α] [DecidableEq α]
variable {U : Finset α} {H : α → Finset (Finset α)} {t : α → Finset α → α} {F : Finset (α × α)}

theorem char2_self {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (x : W) : x + x = 0 := by
  have h := two_smul (ZMod 2) x
  rw [show (2 : ZMod 2) = 0 from rfl, zero_smul] at h
  exact h.symm

theorem char2_four {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (x y : W) :
    x + y + y + x = 0 := by
  rw [show x + y + y + x = (x + x) + (y + y) by abel, char2_self, char2_self, add_zero]

theorem card_fiber_fst (u' : ↥U) (Q : α → Prop) [DecidablePred Q] :
    (univ.filter (fun q : ↥U × α => Q q.2 ∧ q.1 = u')).card = (univ.filter Q).card := by
  have : univ.filter (fun q : ↥U × α => Q q.2 ∧ q.1 = u') =
      (univ.filter Q).map ⟨fun a => (u', a), fun a b h => by simpa using h⟩ := by
    ext ⟨x, a⟩
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨a, h1, rfl⟩
    · rintro ⟨b, hb, hba⟩
      have h1 : u' = x := congrArg Prod.fst hba
      have h2 : b = a := congrArg Prod.snd hba
      subst h1; subst h2; exact ⟨hb, rfl⟩
  rw [this, card_map]

open Classical in
theorem ts_dimension {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Nonempty α]
    (hyp : TSHyp U H t F)
    (heul : ∀ x, (F.filter (fun p => p.1 = x)).card = (F.filter (fun p => p.2 = x)).card)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hcut : ∀ S ⊆ U, lam * S.card * (U \ S).card ≤
      ((F.filter (fun p => p.1 ∈ S ∧ p.2 ∈ U \ S)).card : ℝ))
    (v : α → W) (hsum : ∀ u ∈ U, ∀ e ∈ H u, v u = ∑ x ∈ e, v x) (r : ℕ)
    (hγ : (2 * lam) ^ 2 * (U.card : ℝ) ^ 2 / (16 * (Fintype.card α : ℝ) ^ 2) ≤ 1)
    (hr : (U.card : ℝ) * (U.card + 1) *
      (1 - (2 * lam) ^ 2 * (U.card : ℝ) ^ 2 / (16 * (Fintype.card α : ℝ) ^ 2)) ^ r ≤ 1) :
    (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (fun u : ↥U => v u))) : ℝ) ≤
      60 * (r * Real.logb 2 (Fintype.card α) + Real.logb 2 (U.card + 1)) := by
  let β : ↥U → α → Bool → α := fun u a o => if o then partnerOf H t F u a else a
  have hτmem : ∀ (u : ↥U) (a : α), IsRealT H t F u a → t u (edgeOf H t F u a) ∈ U :=
    fun u a h => (hyp.hF _ (edgeOf_spec h).2.2.2).2.1
  let τ : ↥U → α → Bool → ↥U := fun u a o =>
    if h : o = true ∧ IsRealT H t F u a then ⟨t u (edgeOf H t F u a), hτmem u a h.2⟩ else u
  have hcardU : Fintype.card ↥U = U.card := Fintype.card_coe U
  have hτr : ∀ (u : ↥U) (a : α) (hr : IsRealT H t F u a),
      τ u a true = ⟨t u (edgeOf H t F u a), hτmem u a hr⟩ := fun u a hr => dif_pos ⟨rfl, hr⟩
  have hτn : ∀ (u : ↥U) (a : α), ¬ IsRealT H t F u a → τ u a true = u :=
    fun u a hr => dif_neg (fun h => hr h.2)
  have key := dimension_bound (Ω := ↥U) (Λ := α) (fun u : ↥U => v u) v β τ ?hpar ?hlazy
    ?hright ?hdbl (2 * lam) (by positivity) ?hcut r (by rw [hcardU]; exact hγ)
    (by rw [hcardU]; exact hr)
  · rw [hcardU] at key; exact key
  case hpar =>
    intro u a o
    cases o with
    | false => simp only [β, τ, Bool.false_eq_true, false_and, dite_false, if_false]
               exact char2_four _ _
    | true =>
      by_cases hr : IsRealT H t F u a
      · have h1 := hsum u u.2 _ (edgeOf_spec hr).1
        rw [sum_edge hyp u.2 hr v] at h1
        simp only [β, τ, if_true, true_and, dif_pos hr]
        rw [show v ↑u + v a + v (partnerOf H t F (↑u) a) + v (t (↑u) (edgeOf H t F (↑u) a)) =
          v u + (v a + v (partnerOf H t F (↑u) a) + v (t (↑u) (edgeOf H t F (↑u) a))) by abel,
          ← h1, char2_self]
      · simp only [β, τ, if_true, true_and, dif_neg hr, partner_not_real hr]
        exact char2_four _ _
  case hlazy =>
    intro u a; simp [β, τ]
  case hright =>
    intro u b
    have : univ.filter (fun p : α × Bool => β u p.1 p.2 = b) =
        {(b, false), (partnerOf H t F u b, true)} := by
      ext ⟨a, o⟩
      cases o with
      | false => simp [β]
      | true =>
        simp only [β, mem_filter, mem_univ, true_and, if_true, mem_insert, mem_singleton,
          Prod.mk.injEq, Bool.true_eq_false, and_false, and_true, false_or]
        constructor
        · intro h; rw [← h, partner_invol hyp u.2]
        · intro h; rw [h, partner_invol hyp u.2]
    rw [this, card_pair]; simp
  case hdbl =>
    intro u'
    have hsplit : univ.filter (fun p : ↥U × α => τ p.1 p.2 true = u') =
        univ.filter (fun q : ↥U × α => IsRealT H t F q.1 q.2 ∧
          t q.1 (edgeOf H t F q.1 q.2) = (u' : α)) ∪
        univ.filter (fun q : ↥U × α => ¬ IsRealT H t F q.1 q.2 ∧ q.1 = u') := by
      ext q
      simp only [mem_filter, mem_univ, true_and, mem_union]
      by_cases hr : IsRealT H t F q.1 q.2
      · rw [hτr _ _ hr]
        simp only [hr, true_and, not_true_eq_false, false_and, or_false]
        constructor
        · intro h; rw [← h]
        · intro h; exact Subtype.ext h
      · rw [hτn _ _ hr]
        simp [hr]
    rw [hsplit, card_union_of_disjoint]
    · have hA1 := count_real hyp (fun _ z => z = (u' : α))
      beta_reduce at hA1
      rw [show (univ.filter (fun q : ↥U × α => IsRealT H t F q.1 q.2 ∧
          t q.1 (edgeOf H t F q.1 q.2) = (u' : α))).card =
          2 * (F.filter (fun p => p.2 = (u' : α))).card by convert hA1]
      have h2 := card_fiber_fst u' (fun a => ¬ IsRealT H t F u' a)
      have h3 := count_real hyp (fun x _ => x = (u' : α))
      beta_reduce at h3
      have h4 : (univ.filter (fun q : ↥U × α => IsRealT H t F q.1 q.2 ∧ (q.1 : α) = u')).card =
          (univ.filter (fun a => IsRealT H t F u' a)).card := by
        rw [← card_fiber_fst u' (fun a => IsRealT H t F u' a)]
        congr 1; ext q; simp only [mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          have : q.1 = u' := Subtype.ext h2
          subst this; exact ⟨h1, rfl⟩
        · rintro ⟨h1, rfl⟩; exact ⟨h1, rfl⟩
      rw [show (univ.filter (fun q : ↥U × α => IsRealT H t F q.1 q.2 ∧ (q.1 : α) = u')).card =
          2 * (F.filter (fun p => p.1 = (u' : α))).card by convert h3] at h4
      have h5 := card_filter_add_card_filter_not (s := (univ : Finset α))
        (fun a => IsRealT H t F u' a)
      rw [card_univ] at h5
      have h2' : (univ.filter (fun q : ↥U × α => ¬ IsRealT H t F q.1 q.2 ∧ q.1 = u')).card =
          (univ.filter (fun a => ¬ IsRealT H t F u' a)).card := by
        rw [← h2]; congr 1; apply filter_congr; rintro q -
        constructor
        · rintro ⟨h, rfl⟩; exact ⟨h, rfl⟩
        · rintro ⟨h, rfl⟩; exact ⟨h, rfl⟩
      rw [h2']
      have := heul (u' : α)
      omega
    · rw [disjoint_filter]
      rintro q - ⟨h1, -⟩ ⟨h2, -⟩
      exact h2 h1
  case hcut =>
    intro S
    set S' : Finset α := S.map (Function.Embedding.subtype _)
    have hS'U : S' ⊆ U := by
      intro x hx; simp only [S', mem_map, Function.Embedding.coe_subtype] at hx
      obtain ⟨y, -, rfl⟩ := hx; exact y.2
    have hmemS : ∀ y : ↥U, (y : α) ∈ S' ↔ y ∈ S := by
      intro y; simp [S']
    have hB : univ.filter (fun p : ↥U × α => p.1 ∈ S ∧ τ p.1 p.2 true ∉ S) =
        univ.filter (fun q : ↥U × α => IsRealT H t F q.1 q.2 ∧
          ((q.1 : α) ∈ S' ∧ t q.1 (edgeOf H t F q.1 q.2) ∉ S')) := by
      ext q
      simp only [mem_filter, mem_univ, true_and]
      by_cases hr : IsRealT H t F q.1 q.2
      · rw [hτr _ _ hr, hmemS, hmemS ⟨_, hτmem _ _ hr⟩]
        simp [hr]
      · rw [hτn _ _ hr]
        simp [hr]
    have hA := count_real hyp (fun x z => x ∈ S' ∧ z ∉ S')
    beta_reduce at hA
    rw [hB, show (univ.filter (fun q : ↥U × α => IsRealT H t F q.1 q.2 ∧
          ((q.1 : α) ∈ S' ∧ t q.1 (edgeOf H t F q.1 q.2) ∉ S'))).card =
          2 * (F.filter (fun p => p.1 ∈ S' ∧ p.2 ∉ S')).card by convert hA]
    have hc := hcut S' hS'U
    have hF2 : F.filter (fun p => p.1 ∈ S' ∧ p.2 ∈ U \ S') =
        F.filter (fun p => p.1 ∈ S' ∧ p.2 ∉ S') := by
      apply filter_congr
      intro p hp
      have := (hyp.hF p hp).2.1
      simp [this]
    rw [hF2] at hc
    have hS'card : S'.card = S.card := card_map _
    have hsd : ((U \ S').card : ℝ) = ((univ \ S).card : ℝ) := by
      rw [card_sdiff_of_subset hS'U, card_sdiff_of_subset (subset_univ _), card_univ, hcardU,
        hS'card]
    rw [hS'card, hsd] at hc
    push_cast
    nlinarith

end TS2

end MainAux

namespace MainAux

open Finset

theorem numeric (δ L r l1 : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hL : 1 ≤ L) (hr0 : 0 ≤ r)
    (hr : r ≤ 3 * L / ((δ / 9) ^ 10 / 2 ^ 22) + 1) (hl : l1 ≤ 2 * L) :
    16 / (δ / 9) ^ 2 * (60 * (r * L + l1)) ≤ 2 ^ 90 * δ ^ (-14 : ℤ) * L ^ 2 := by
  set θ := δ / 9 with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  have hT0 : 0 < θ ^ 10 := by positivity
  have hT1 : θ ^ 10 ≤ 1 := pow_le_one₀ hθ0.le hθ1
  have hL0 : 0 ≤ L := by linarith
  have h1 : r * L ≤ 3 * 2 ^ 22 * L ^ 2 / θ ^ 10 + L := by
    have := mul_le_mul_of_nonneg_right hr hL0
    calc r * L ≤ (3 * L / (θ ^ 10 / 2 ^ 22) + 1) * L := this
      _ = 3 * 2 ^ 22 * L ^ 2 / θ ^ 10 + L := by field_simp
  have h2 : 3 * L ≤ 3 * L ^ 2 / θ ^ 10 := by
    rw [le_div_iff₀ hT0]
    nlinarith
  have h3 : r * L + l1 ≤ 2 ^ 24 * L ^ 2 / θ ^ 10 := by
    have : 3 * 2 ^ 22 * L ^ 2 / θ ^ 10 + 3 * L ^ 2 / θ ^ 10 ≤ 2 ^ 24 * L ^ 2 / θ ^ 10 := by
      rw [← add_div]; apply div_le_div_of_nonneg_right _ hT0.le; nlinarith
    linarith
  have h4 : 16 / θ ^ 2 * (60 * (r * L + l1)) ≤ 16 / θ ^ 2 * (60 * (2 ^ 24 * L ^ 2 / θ ^ 10)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
  have h5 : 16 / θ ^ 2 * (60 * (2 ^ 24 * L ^ 2 / θ ^ 10)) =
      (960 * 2 ^ 24 * 9 ^ 12) * L ^ 2 / δ ^ 12 := by
    rw [hθ]; field_simp; ring
  have h6 : δ ^ (-14 : ℤ) = 1 / δ ^ 14 := by
    rw [zpow_neg, one_div]; norm_cast
  have h7 : (960 * 2 ^ 24 * 9 ^ 12) * L ^ 2 / δ ^ 12 ≤ 2 ^ 90 * (1 / δ ^ 14) * L ^ 2 := by
    have hd12 : 0 < δ ^ 12 := by positivity
    have hd14 : 0 < δ ^ 14 := by positivity
    have hdd : δ ^ 14 ≤ δ ^ 12 := pow_le_pow_of_le_one hδ0.le hδ1.le (by norm_num)
    rw [div_le_iff₀ hd12]
    have hL2 : 0 ≤ L ^ 2 := by positivity
    have : 2 ^ 90 * (1 / δ ^ 14) * L ^ 2 * δ ^ 12 = 2 ^ 90 * L ^ 2 * (δ ^ 12 / δ ^ 14) := by ring
    rw [this]
    have h8 : 1 ≤ δ ^ 12 / δ ^ 14 := by rw [le_div_iff₀ hd14]; linarith
    nlinarith
  rw [h6]; linarith

end MainAux

namespace MainAux

open Finset

theorem hr_bound (N m L γs γU : ℝ) (r : ℕ) (hN : 2 ≤ N) (hm0 : 0 ≤ m) (hmN : m ≤ N)
    (hL : Real.log N ≤ L) (hγs0 : 0 < γs) (hγ : γs ≤ γU) (hγU : γU ≤ 1)
    (hr : 3 * L / γs ≤ r) : m * (m + 1) * (1 - γU) ^ r ≤ 1 := by
  have h1 : (1 - γU) ^ r ≤ (1 - γs) ^ r := pow_le_pow_left₀ (by linarith) (by linarith) r
  have h2 : (1 - γs) ^ r ≤ Real.exp (-γs) ^ r :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-γs)]) r
  have h3 : Real.exp (-γs) ^ r = Real.exp (-(γs * r)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have h4 : 3 * L ≤ γs * r := by
    rw [div_le_iff₀ hγs0] at hr; linarith
  have h5 : Real.exp (-(γs * r)) ≤ Real.exp (-(3 * L)) := Real.exp_le_exp.2 (by linarith)
  have h6 : N ^ 3 ≤ Real.exp (3 * L) := by
    have : N ^ 3 = Real.exp (((3 : ℕ) : ℝ) * Real.log N) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    rw [this]; exact Real.exp_le_exp.2 (by push_cast; linarith)
  have h7 : m * (m + 1) ≤ N ^ 3 := by
    have h7a : m * (m + 1) ≤ N * (N + 1) := by nlinarith
    have hNN : N + 1 ≤ N ^ 2 := by nlinarith
    have h7b : N * (N + 1) ≤ N * N ^ 2 := mul_le_mul_of_nonneg_left hNN (by linarith)
    have : N * N ^ 2 = N ^ 3 := by ring
    linarith
  have h8 : 0 ≤ (1 - γU) ^ r := pow_nonneg (by linarith) r
  have hexp : Real.exp (3 * L) * Real.exp (-(3 * L)) = 1 := by
    rw [← Real.exp_add]; simp
  calc m * (m + 1) * (1 - γU) ^ r ≤ N ^ 3 * Real.exp (-(3 * L)) := by
        apply mul_le_mul h7 _ h8 (by positivity)
        calc (1 - γU) ^ r ≤ (1 - γs) ^ r := h1
          _ ≤ Real.exp (-γs) ^ r := h2
          _ = Real.exp (-(γs * r)) := h3
          _ ≤ _ := h5
    _ ≤ Real.exp (3 * L) * Real.exp (-(3 * L)) :=
        mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
    _ = 1 := hexp

theorem log_le_logb2 (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ Real.logb 2 x := by
  rw [Real.logb]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hlN : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [le_div_iff₀ hl2]; nlinarith

set_option maxHeartbeats 1000000 in
open Classical in
theorem step_exists {k n : ℕ} (C : CodeModel k n) (δ ε : ℝ) (hε1 : ε < 1 / 2)
    (hcorrect : Corrects C δ ε) (θ s lam B : ℝ) (r : ℕ)
    (hθ0 : 0 < θ) (hθN : θ * ((2 * n : ℕ) : ℝ) = 2 * δ * n / 9) (hs : s = θ ^ 2 * ((2 * n : ℕ) : ℝ) / 16)
    (hlam0 : 0 ≤ lam)
    (hγf : ∀ m : ℝ, 0 ≤ m → m ≤ ((2 * n : ℕ) : ℝ) → (2 * lam) ^ 2 * m ^ 2 / (16 * ((2 * n : ℕ) : ℝ) ^ 2) ≤ 1)
    (hrf : ∀ m : ℝ, s ≤ m → m ≤ ((2 * n : ℕ) : ℝ) →
      m * (m + 1) * (1 - (2 * lam) ^ 2 * m ^ 2 / (16 * ((2 * n : ℕ) : ℝ) ^ 2)) ^ r ≤ 1)
    (hB : 60 * (r * Real.logb 2 ((2 * n : ℕ) : ℝ) + Real.logb 2 (((2 * n : ℕ) : ℝ) + 1)) ≤ B)
    (hlamv : lam = θ ^ 3 / 64) (hsmall : 3 ≤ δ * n)
    (v : Fin (2 * n) → (Fin k → Bit)) (hv : v = paddedRow C)
    (U0 : Submodule Bit (Fin k → Bit)) (hne : (univ.filter (fun i => v i ∉ U0)).Nonempty) :
      ∃ U1 : Submodule Bit (Fin k → Bit), U0 ≤ U1 ∧
        U1 ≤ U0 ⊔ Submodule.span Bit (Set.range v) ∧
        (Module.finrank Bit ↥U1 : ℝ) ≤ Module.finrank Bit ↥U0 + B ∧
        ((univ.filter (fun i => v i ∉ U1)).card : ℝ) + s ≤
          (univ.filter (fun i => v i ∉ U0)).card := by
  set V := univ.filter (fun i => v i ∉ U0) with hVdef
  have hmatch : ∀ x ∈ V, ∃ H : Finset (Finset (Fin (2 * n))), IsRecoveryMatching x H ∧
      δ * n < 3 * (H.card : ℝ) + 1 ∧ ∀ e ∈ H, v x = ∑ a ∈ e, v a := by
    intro x hx
    have hxv : v x ∉ U0 := (mem_filter.1 hx).2
    have hxn : x.val < n := by
      by_contra hge
      apply hxv
      have : v x = 0 := by
        simp only [hv, paddedRow, dif_neg hge]
      rw [this]; exact U0.zero_mem
    have hu : codeRow C ⟨x.val, hxn⟩ ≠ 0 := by
      intro h0; apply hxv
      have : v x = 0 := by simp only [hv, paddedRow, dif_pos hxn, h0]
      rw [this]; exact U0.zero_mem
    obtain ⟨H, h1, h2, h3⟩ := recovery_matching_of_corrects C δ ε hε1 hcorrect ⟨x.val, hxn⟩ hu
    exact ⟨H, h1, h2, by rw [hv]; exact h3⟩
  let Hf : Fin (2 * n) → Finset (Finset (Fin (2 * n))) := fun x =>
    if h : x ∈ V then (hmatch x h).choose else ∅
  have hHf : ∀ x ∈ V, IsRecoveryMatching x (Hf x) ∧ δ * n < 3 * ((Hf x).card : ℝ) + 1 ∧
      ∀ e ∈ Hf x, v x = ∑ a ∈ e, v a := by
    intro x hx
    simp only [Hf, dif_pos hx]
    exact (hmatch x hx).choose_spec
  let tgt : Fin (2 * n) → Finset (Fin (2 * n)) → Fin (2 * n) := fun x e =>
    if h : ∃ a ∈ e, v a ∉ U0 then h.choose else x
  have htgt : ∀ x ∈ V, ∀ e ∈ Hf x, tgt x e ∈ e ∧ v (tgt x e) ∉ U0 := by
    intro x hx e he
    have hex : ∃ a ∈ e, v a ∉ U0 := by
      by_contra hall
      push Not at hall
      apply (mem_filter.1 hx).2
      rw [(hHf x hx).2.2 e he]
      exact U0.sum_mem hall
    simp only [tgt, dif_pos hex]
    exact hex.choose_spec
  let R : Fin (2 * n) → Fin (2 * n) → Prop := fun y z => y ∈ V ∧ ∃ e ∈ Hf y, tgt y e = z
  have hcardV : V.card ≤ (2 * n) := by
    calc V.card ≤ (univ : Finset (Fin (2 * n))).card := card_le_univ _
      _ = (2 * n) := by simp
  have hdeg : ∀ x ∈ V, θ * ((2 * n : ℕ) : ℝ) ≤ ((V.filter (fun y => R x y)).card : ℝ) := by
    intro x hx
    have hsub : (Hf x).image (tgt x) ⊆ V.filter (fun y => R x y) := by
      intro z hz
      obtain ⟨e, he, rfl⟩ := mem_image.1 hz
      refine mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, (htgt x hx e he).2⟩, hx, e, he, rfl⟩
    have hinj : Set.InjOn (tgt x) (Hf x : Set (Finset (Fin (2 * n)))) := by
      intro e he e' he' heq
      by_contra hne
      have hd := (hHf x hx).1.2 e he e' he' hne
      exact Finset.disjoint_left.1 hd (htgt x hx e he).1 (heq ▸ (htgt x hx e' he').1)
    have hc := card_le_card hsub
    rw [card_image_of_injOn hinj] at hc
    have h2 := (hHf x hx).2.1
    have : (((Hf x).card : ℕ) : ℝ) ≤ ((V.filter (fun y => R x y)).card : ℝ) := by
      exact_mod_cast hc
    rw [hθN]; linarith
  obtain ⟨U, F, hUV, hUne, hUcard, hFR, heul, hcut⟩ :=
    eulerian_cut_dense_piece V R (2 * n) θ hθ0 hne hcardV hdeg
  rw [← hlamv] at hcut
  have : Nonempty (Fin (2 * n)) := ⟨hne.choose⟩
  have hyp : TSHyp U Hf tgt F := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u hu e he; exact ((hHf u (hUV hu)).1.1 e he).1
    · intro u hu e he; exact (htgt u (hUV hu) e he).1
    · intro u hu e he e' he' hne; exact (hHf u (hUV hu)).1.2 e he e' he' hne
    · intro p hp
      obtain ⟨⟨_, e, he, hte⟩, h1, h2⟩ := hFR p hp
      exact ⟨h1, h2, e, he, hte⟩
  have hUN : (U.card : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
    have := card_le_card hUV; exact_mod_cast this.trans hcardV
  have hUs : s ≤ U.card := by rw [hs]; exact hUcard
  have hγU := hγf (U.card : ℝ) (by positivity) hUN
  have hrU := hrf (U.card : ℝ) hUs hUN
  have hdim := ts_dimension (W := (Fin k → Bit) ⧸ U0) hyp heul lam hlam0 hcut
    (fun a => U0.mkQ (v a)) (by
      intro u hu e he
      simp only [← map_sum]
      rw [← (hHf u (hUV hu)).2.2 e he]) r (by simpa using hγU) (by simpa using hrU)
  simp only [Fintype.card_fin] at hdim
  set T := Submodule.span Bit ((fun a => v a) '' (U : Set (Fin (2 * n)))) with hT
  refine ⟨U0 ⊔ T, le_sup_left, ?_, ?_, ?_⟩
  · apply sup_le_sup_left
    apply Submodule.span_mono
    rintro _ ⟨a, -, rfl⟩; exact ⟨a, rfl⟩
  · have h1 := finrank_sup_le_quot U0 T
    have hmap : T.map U0.mkQ =
        Submodule.span Bit (Set.range (fun u : ↥U => U0.mkQ (v u))) := by
      rw [hT, Submodule.map_span]
      congr 1
      ext y; simp
    rw [hmap] at h1
    have h2 : Real.logb 2 ((U.card : ℝ) + 1) ≤ Real.logb 2 (((2 * n : ℕ) : ℝ) + 1) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
    have h3 : (Module.finrank Bit ↥(U0 ⊔ T) : ℝ) ≤ Module.finrank Bit ↥U0 +
        Module.finrank Bit ↥(Submodule.span Bit (Set.range (fun u : ↥U => U0.mkQ (v u)))) := by
      exact_mod_cast h1
    have : (60 : ℝ) * (r * Real.logb 2 ((2 * n : ℕ) : ℝ) + Real.logb 2 ((U.card : ℝ) + 1)) ≤
        60 * (r * Real.logb 2 ((2 * n : ℕ) : ℝ) + Real.logb 2 (((2 * n : ℕ) : ℝ) + 1)) := by linarith
    linarith
  · have hsub : univ.filter (fun i => v i ∉ U0 ⊔ T) ⊆ V \ U := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      rw [mem_sdiff]
      refine ⟨mem_filter.2 ⟨mem_univ _, fun h => hi (Submodule.mem_sup_left h)⟩, fun hiU => ?_⟩
      apply hi
      apply Submodule.mem_sup_right
      exact Submodule.subset_span ⟨i, hiU, rfl⟩
    have hc := card_le_card hsub
    rw [card_sdiff_of_subset hUV] at hc
    have hUleV := card_le_card hUV
    have : ((univ.filter (fun i => v i ∉ U0 ⊔ T)).card : ℝ) + U.card ≤ V.card := by
      have : (univ.filter (fun i => v i ∉ U0 ⊔ T)).card + U.card ≤ V.card := by omega
      exact_mod_cast this
    linarith

set_option maxHeartbeats 1000000 in
open Classical in
theorem main_bound {k n : ℕ} (hn : 0 < n) (C : CodeModel k n) (δ ε : ℝ) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε1 : ε < 1 / 2) (hcorrect : Corrects C δ ε) :
    (k : ℝ) ≤ (2 : ℝ) ^ 90 * δ ^ (-14 : ℤ) * (Real.logb 2 (2 * (n : ℝ))) ^ 2 := by
  set L := Real.logb 2 (2 * (n : ℝ)) with hLdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.logb_self_eq_one (b := 2) (by norm_num)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  have hD : δ ^ (-14 : ℤ) = 1 / δ ^ 14 := by rw [zpow_neg, one_div]; norm_cast
  -- k ≤ n
  have hkn : k ≤ n := by
    have := LinearMap.finrank_le_finrank_of_injective (f := C.encoding) C.injective
    simpa using this
  by_cases hsmall : δ * n < 3
  · have hk : (k : ℝ) < 3 / δ := by
      rw [lt_div_iff₀ hδ]
      have : (k : ℝ) ≤ n := by exact_mod_cast hkn
      nlinarith
    have hd14 : δ ^ 14 ≤ δ := by
      calc δ ^ 14 ≤ δ ^ 1 := pow_le_pow_of_le_one hδ.le hδ1.le (by norm_num)
        _ = δ := pow_one δ
    have h3 : 3 / δ ≤ 3 / δ ^ 14 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hd14
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    rw [hD]
    have : 3 / δ ^ 14 ≤ 2 ^ 90 * (1 / δ ^ 14) * L ^ 2 := by
      have hp : 0 < 1 / δ ^ 14 := by positivity
      have : 3 / δ ^ 14 = 3 * (1 / δ ^ 14) := by ring
      rw [this]; nlinarith
    linarith
  push Not at hsmall
  -- main case
  set N : ℕ := 2 * n with hNdef
  have hNr : (N : ℝ) = 2 * n := by rw [hNdef]; push_cast; ring
  have hN2 : (2 : ℝ) ≤ N := by rw [hNr]; linarith
  have hLN : L = Real.logb 2 N := by rw [hLdef, hNr]
  set θ : ℝ := δ / 9 with hθ
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by rw [hθ]; linarith
  set s : ℝ := θ ^ 2 * N / 16 with hs
  have hs0 : 0 < s := by positivity
  set lam : ℝ := θ ^ 3 / 64 with hlam
  have hlam0 : 0 ≤ lam := by positivity
  set γs : ℝ := (2 * lam) ^ 2 * s ^ 2 / (16 * (N : ℝ) ^ 2) with hγs
  have hγs0 : 0 < γs := by positivity
  have hγsv : γs = θ ^ 10 / 2 ^ 22 := by
    rw [hγs, hs, hlam]; field_simp; ring
  set r : ℕ := ⌈3 * L / γs⌉₊ with hrdef
  set B : ℝ := 60 * (r * L + Real.logb 2 (N + 1)) with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Real.logb 2 ((N : ℝ) + 1) := Real.logb_nonneg (by norm_num) (by linarith)
    positivity
  set v : Fin N → (Fin k → Bit) := paddedRow C with hv
  have hγf : ∀ m : ℝ, 0 ≤ m → m ≤ N → (2 * lam) ^ 2 * m ^ 2 / (16 * (N : ℝ) ^ 2) ≤ 1 := by
    intro m hm0 hm
    rw [div_le_one (by positivity)]
    have h2l : 2 * lam ≤ 1 := by
      rw [hlam]
      have : θ ^ 3 ≤ 1 := pow_le_one₀ hθ0.le hθ1
      linarith
    have h2l0 : 0 ≤ 2 * lam := by positivity
    have : (2 * lam) ^ 2 ≤ 1 := by nlinarith
    have : m ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hrf : ∀ m : ℝ, s ≤ m → m ≤ N →
      m * (m + 1) * (1 - (2 * lam) ^ 2 * m ^ 2 / (16 * (N : ℝ) ^ 2)) ^ r ≤ 1 := by
    intro m hsm hmN
    have hm0 : 0 ≤ m := le_trans hs0.le hsm
    refine hr_bound N m L γs _ r hN2 hm0 hmN ?_ hγs0 ?_ (hγf m hm0 hmN) (Nat.le_ceil _)
    · rw [hLN]; exact log_le_logb2 _ (by linarith)
    · rw [hγs]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
  have step := fun U0 hne => step_exists C δ ε hε1 hcorrect θ s lam B r hθ0
    (by rw [hθ, hNr]; ring) hs hlam0 hγf hrf (by rw [hB, hLN]) hlam hsmall v rfl U0 hne
  have hit := iterate_bound (K := Bit) v s B hs0 hB0 step
  have hk : spanDimension (paddedRow C) = k := padded_span_dimension C
  unfold spanDimension at hk
  rw [hv, hk] at hit
  simp only [Fintype.card_fin] at hit
  have hNs : (N : ℝ) / s = 16 / θ ^ 2 := by
    rw [hs]; field_simp
  rw [hNs] at hit
  have hrle : (r : ℝ) ≤ 3 * L / (θ ^ 10 / 2 ^ 22) + 1 := by
    rw [← hγsv]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hl1 : Real.logb 2 ((N : ℝ) + 1) ≤ 2 * L := by
    have : Real.logb 2 ((N : ℝ) + 1) ≤ Real.logb 2 (2 * N) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num),
      ← hLN] at this
    linarith
  have hnum := numeric δ L r (Real.logb 2 ((N : ℝ) + 1)) hδ hδ1 hL1 (by positivity)
    (by rw [hθ] at hrle; exact hrle) hl1
  rw [← hθ] at hnum
  calc (k : ℝ) ≤ 16 / θ ^ 2 * B := hit
    _ ≤ _ := hnum

end MainAux

end BinaryThreeLCC.JM

open BinaryThreeLCC.Main

theorem solution {k n : ℕ} (hn : 0 < n)
    (C : CodeModel k n) (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 ≤ ε) (hε1 : ε < 1 / 2) (hcorrect : Corrects C δ ε) :
    (k : ℝ) ≤ (2 : ℝ) ^ 90 * δ ^ (-14 : ℤ) * (Real.logb 2 (2 * (n : ℝ))) ^ 2 ∧
    (2 : ℝ) ^ ((2 : ℝ) ^ (-45 : ℤ) * δ ^ 7 * Real.sqrt k) ≤ 2 * (n : ℝ) ∧
    (2 ≤ n → (2 : ℝ) ^ ((2 : ℝ) ^ (-46 : ℤ) * δ ^ 7 * Real.sqrt k) ≤ (n : ℝ)) := by
  have hA := BinaryThreeLCC.JM.MainAux.main_bound hn C δ ε hδ hδ1 hε1 hcorrect
  set L := Real.logb 2 (2 * (n : ℝ)) with hLdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.logb_self_eq_one (b := 2) (by norm_num)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  have hD : δ ^ (-14 : ℤ) = (δ ^ 7)⁻¹ ^ 2 := by
    rw [inv_pow, ← pow_mul, zpow_neg]; norm_cast
  have h45 : (2 : ℝ) ^ (-45 : ℤ) = ((2 : ℝ) ^ 45)⁻¹ := by rw [zpow_neg]; norm_cast
  have h46 : (2 : ℝ) ^ (-46 : ℤ) = ((2 : ℝ) ^ 45)⁻¹ / 2 := by
    rw [zpow_neg]; norm_cast; ring
  have hd7 : 0 < δ ^ 7 := by positivity
  -- √k ≤ 2^45 δ^-7 L
  have hsq : Real.sqrt k ≤ 2 ^ 45 * (δ ^ 7)⁻¹ * L := by
    rw [Real.sqrt_le_left (by positivity)]
    calc (k : ℝ) ≤ 2 ^ 90 * δ ^ (-14 : ℤ) * L ^ 2 := hA
      _ = (2 ^ 45 * (δ ^ 7)⁻¹ * L) ^ 2 := by rw [hD]; ring
  have hE : (2 : ℝ) ^ (-45 : ℤ) * δ ^ 7 * Real.sqrt k ≤ L := by
    rw [h45]
    calc ((2 : ℝ) ^ 45)⁻¹ * δ ^ 7 * Real.sqrt k
        ≤ ((2 : ℝ) ^ 45)⁻¹ * δ ^ 7 * (2 ^ 45 * (δ ^ 7)⁻¹ * L) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = L := by field_simp
  have h2n : (0 : ℝ) < 2 * n := by linarith
  refine ⟨hA, ?_, ?_⟩
  · calc (2 : ℝ) ^ ((2 : ℝ) ^ (-45 : ℤ) * δ ^ 7 * Real.sqrt k) ≤ (2 : ℝ) ^ L :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hE
      _ = 2 * n := Real.rpow_logb (by norm_num) (by norm_num) h2n
  · intro hn2
    have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hLn : L = 1 + Real.logb 2 n := by
      rw [hLdef, Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)]
    have hlogn : 1 ≤ Real.logb 2 n := by
      rw [← Real.logb_self_eq_one (b := 2) (by norm_num)]
      exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hn2'
    have hE' : (2 : ℝ) ^ (-46 : ℤ) * δ ^ 7 * Real.sqrt k ≤ Real.logb 2 n := by
      have : (2 : ℝ) ^ (-46 : ℤ) * δ ^ 7 * Real.sqrt k =
          ((2 : ℝ) ^ (-45 : ℤ) * δ ^ 7 * Real.sqrt k) / 2 := by rw [h46, h45]; ring
      rw [this]
      have h2E := div_le_div_of_nonneg_right hE (by norm_num : (0:ℝ) ≤ 2)
      calc (2 : ℝ) ^ (-45 : ℤ) * δ ^ 7 * Real.sqrt k / 2 ≤ L / 2 := h2E
        _ ≤ Real.logb 2 n := by rw [hLn]; linarith
    calc (2 : ℝ) ^ ((2 : ℝ) ^ (-46 : ℤ) * δ ^ 7 * Real.sqrt k) ≤ (2 : ℝ) ^ Real.logb 2 n :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hE'
      _ = n := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)

