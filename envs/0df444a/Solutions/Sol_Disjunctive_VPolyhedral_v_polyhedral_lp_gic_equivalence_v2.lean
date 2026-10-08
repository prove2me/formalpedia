-- Prove2me | solution 1 for Disjunctive.VPolyhedral.v_polyhedral_lp_gic_equivalence_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T07:22:19.8024+00:00
-- url     : https://prove2.me/submissions/d92de909-2f1c-4c6f-995a-31134f637a2e

import Mathlib
import Definitions.Def_Disjunctive_VPolyhedral_Basic

set_option autoImplicit false

namespace P2MFarkasDE

open Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finitely generated cone. -/
def coneSet (v : ι → E) : Set E := {x | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ x = ∑ i, c i • v i}

lemma sum_ext (v : ι → E) (s : Finset ι) (d : s → ℝ) :
    ∑ i : s, d i • v i = ∑ i, (if h : i ∈ s then d ⟨i, h⟩ else 0) • v i := by
  have hz : ∀ i ∈ (univ : Finset ι), i ∉ s →
      (if h : i ∈ s then d ⟨i, h⟩ else 0) • v i = 0 := by
    intro i _ hi; simp [hi]
  rw [← Finset.sum_subset (Finset.subset_univ s) hz, ← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [i.2]

lemma sum_restrict (v : ι → E) (s : Finset ι) (c : ι → ℝ) (hc : ∀ i ∉ s, c i = 0) :
    ∑ i : s, c i • v i = ∑ i, c i • v i := by
  rw [Finset.sum_coe_sort s (fun i => c i • v i)]
  exact Finset.sum_subset (Finset.subset_univ s) (fun i _ hi => by simp [hc i hi])

lemma cara (v : ι → E) (x : E) : ∀ k : ℕ, ∀ c : ι → ℝ, (∀ i, 0 ≤ c i) → x = ∑ i, c i • v i →
    (univ.filter (fun i => c i ≠ 0)).card = k →
    ∃ s : Finset ι, LinearIndependent ℝ (fun i : s => v i) ∧
      ∃ c' : ι → ℝ, (∀ i, 0 ≤ c' i) ∧ (∀ i ∉ s, c' i = 0) ∧ x = ∑ i, c' i • v i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro c hc hx hk
  set s := univ.filter (fun i => c i ≠ 0) with hs
  by_cases hli : LinearIndependent ℝ (fun i : s => v i)
  · exact ⟨s, hli, c, hc, fun i hi => by simpa [hs] using hi, hx⟩
  · obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
    let μ0 : ι → ℝ := fun i => if h : i ∈ s then g ⟨i, h⟩ else 0
    have hμ0 : ∑ i, μ0 i • v i = 0 := by rw [← sum_ext]; exact hg
    have hμ0s : ∀ i, c i = 0 → μ0 i = 0 := fun i hi => by simp [μ0, hs, hi]
    have hμ0i : μ0 i0 ≠ 0 := by
      have : μ0 i0 = g i0 := by simp [μ0, i0.2]
      rw [this]; exact hi0
    obtain ⟨μ, hμsum, hμs, j0, hj0⟩ : ∃ μ : ι → ℝ, ∑ i, μ i • v i = 0 ∧
        (∀ i, c i = 0 → μ i = 0) ∧ ∃ j, 0 < μ j := by
      rcases lt_or_gt_of_ne hμ0i with h | h
      · refine ⟨fun i => - μ0 i, ?_, ?_, i0, ?_⟩
        · simp [neg_smul, Finset.sum_neg_distrib, hμ0]
        · intro i hi; simp [hμ0s i hi]
        · simp only; linarith
      · exact ⟨μ0, hμ0, hμ0s, i0, h⟩
    set T := univ.filter (fun i => 0 < μ i) with hT
    have hTne : T.Nonempty := ⟨j0, by simp [T, hj0]⟩
    obtain ⟨j, hjT, hjmin⟩ := Finset.exists_min_image T (fun i => c i / μ i) hTne
    have hμj : 0 < μ j := by simpa [T] using hjT
    set t := c j / μ j with ht_def
    have ht : 0 ≤ t := div_nonneg (hc j) hμj.le
    let c' : ι → ℝ := fun i => c i - t * μ i
    have hc' : ∀ i, 0 ≤ c' i := by
      intro i
      by_cases hi : 0 < μ i
      · have h1 := hjmin i (by simp [T, hi])
        have h2 : t * μ i ≤ c i := by rwa [le_div_iff₀ hi] at h1
        simp only [c']; linarith
      · push Not at hi
        have : t * μ i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hi
        simp only [c']; linarith [hc i]
    have hx' : x = ∑ i, c' i • v i := by
      simp only [c', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hμsum,
        smul_zero, sub_zero]
      exact hx
    have hcj : c j ≠ 0 := by
      intro h0; have := hμs j h0; linarith
    have hcard : (univ.filter (fun i => c' i ≠ 0)).card < k := by
      rw [← hk]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨j, by simp [hs, hcj], ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not, c', ht_def]
        field_simp
        ring
      · intro i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs]
        intro h hci
        apply h
        simp [c', hci, hμs i hci]
    exact ih _ hcard c' hc' hx' rfl

lemma coneSet_closed (v : ι → E) : IsClosed (coneSet v) := by
  have key : coneSet v = ⋃ s ∈ {s : Finset ι | LinearIndependent ℝ (fun i : s => v i)},
      (Fintype.linearCombination ℝ (fun i : s => v i)) '' {d | ∀ i, 0 ≤ d i} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, coneSet, exists_prop]
    constructor
    · rintro ⟨c, hc, hx⟩
      obtain ⟨s, hli, c', hc', hs, hx'⟩ := cara v x _ c hc hx rfl
      refine ⟨s, hli, fun i => c' i, fun i => hc' i, ?_⟩
      rw [Fintype.linearCombination_apply, sum_restrict v s c' hs, hx']
    · rintro ⟨s, _, d, hd, rfl⟩
      refine ⟨fun i => if h : i ∈ s then d ⟨i, h⟩ else 0, ?_, ?_⟩
      · intro i
        by_cases h : i ∈ s
        · simp only [h, dite_true]; exact hd _
        · simp [h]
      · rw [Fintype.linearCombination_apply, sum_ext]
  rw [key]
  refine Set.Finite.isClosed_biUnion (Set.toFinite _) ?_
  intro s hs
  have hinj : Function.Injective (Fintype.linearCombination ℝ (fun i : s => v i)) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hs
  have hcl : IsClosed {d : s → ℝ | ∀ i, 0 ≤ d i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj)).isClosedMap _ hcl

lemma coneSet_convex (v : ι → E) : Convex ℝ (coneSet v) := by
  rintro x ⟨c, hc, rfl⟩ y ⟨d, hd, rfl⟩ a b ha hb _
  refine ⟨fun i => a * c i + b * d i, fun i => ?_, ?_⟩
  · have := hc i; have := hd i; positivity
  · simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

lemma farkas_cone (v : ι → E) (p : E) (hp : p ∉ coneSet v) :
    ∃ f : StrongDual ℝ E, (∀ i, f (v i) ≤ 0) ∧ 0 < f p := by
  obtain ⟨f, u, hf, hu⟩ :=
    geometric_hahn_banach_closed_point (coneSet_convex v) (coneSet_closed v) hp
  have h0 : (0 : E) ∈ coneSet v := ⟨0, fun _ => le_rfl, by simp⟩
  have hu0 : 0 < u := by simpa using hf 0 h0
  refine ⟨f, fun i => ?_, by linarith⟩
  by_contra hcon
  push Not at hcon
  have hmem : (u / f (v i)) • v i ∈ coneSet v := by
    refine ⟨fun j => if j = i then u / f (v i) else 0, fun j => ?_, ?_⟩
    · dsimp only
      split_ifs
      · positivity
      · exact le_rfl
    · simp [ite_smul]
  have := hf _ hmem
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hcon.ne'] at this
  exact lt_irrefl _ this

theorem affine_farkas {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (α : Fin n → ℝ) (α0 : ℝ) (hne : ({x : Fin n → ℝ | ∀ i, b i ≤ (A.mulVec x) i}).Nonempty)
    (hval : ∀ x ∈ {x : Fin n → ℝ | ∀ i, b i ≤ (A.mulVec x) i}, α0 ≤ dotProduct x α) :
    ∃ u : Fin m → ℝ, Matrix.vecMul u A = α ∧ α0 ≤ dotProduct u b ∧ 0 ≤ u := by
  classical
  let v : Option (Fin m) → (Fin n → ℝ) × ℝ := fun o =>
    match o with
    | none => (0, -1)
    | some i => (A i, b i)
  by_cases hp : ((α, α0) : (Fin n → ℝ) × ℝ) ∈ coneSet v
  · obtain ⟨c, hc, hx⟩ := hp
    refine ⟨fun i => c (some i), ?_, ?_, fun i => hc _⟩
    · rw [Fintype.sum_option] at hx
      have h1 := congrArg Prod.fst hx
      simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, v, smul_zero, zero_add] at h1
      ext j
      rw [h1]
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    · rw [Fintype.sum_option] at hx
      have h2 := congrArg Prod.snd hx
      simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, v, smul_eq_mul] at h2
      rw [h2]
      simp only [dotProduct]
      linarith [hc none]
  · obtain ⟨f, hfv, hfp⟩ := farkas_cone v _ hp
    let y : Fin n → ℝ := fun j => f ((Pi.single j 1 : Fin n → ℝ), (0 : ℝ))
    let s : ℝ := f ((0 : Fin n → ℝ), (1 : ℝ))
    have hf : ∀ z r, f (z, r) = dotProduct z y + r * s := by
      intro z r
      have : ((z, r) : (Fin n → ℝ) × ℝ) =
          ∑ j, z j • ((Pi.single j 1 : Fin n → ℝ), (0 : ℝ)) + r • ((0 : Fin n → ℝ), (1 : ℝ)) := by
        ext k
        · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
        · simp [Prod.snd_sum]
      rw [this]
      simp only [map_add, map_sum, map_smul, smul_eq_mul]
      rfl
    have hgen : ∀ i, dotProduct (A i) y + b i * s ≤ 0 := fun i => by
      rw [← hf]; exact hfv (some i)
    have hs : 0 ≤ s := by
      have := hfv none
      simp only [v] at this
      rw [hf] at this
      simp at this
      linarith
    have hpos : 0 < dotProduct α y + α0 * s := by rw [← hf]; exact hfp
    have hmv : ∀ (z : Fin n → ℝ) (i : Fin m), (A.mulVec z) i = dotProduct (A i) z :=
      fun _ _ => rfl
    obtain ⟨x0, hx0⟩ := hne
    exfalso
    rcases hs.lt_or_eq with hs | hs
    · let x : Fin n → ℝ := (-s⁻¹) • y
      have hx : x ∈ {x : Fin n → ℝ | ∀ i, b i ≤ (A.mulVec x) i} := by
        intro i
        rw [hmv]
        have := hgen i
        simp only [x, dotProduct_smul, smul_eq_mul]
        rw [show -s⁻¹ * dotProduct (A i) y = (-dotProduct (A i) y) / s by ring, le_div_iff₀ hs]
        linarith
      have hv := hval x hx
      have e : dotProduct x α = (-dotProduct α y) / s := by
        simp only [x, smul_dotProduct, smul_eq_mul, dotProduct_comm y α]
        ring
      have : (-dotProduct α y) / s < α0 := by
        rw [div_lt_iff₀ hs]; linarith
      linarith
    · rw [← hs] at hgen hpos
      have hαy : 0 < dotProduct α y := by simpa using hpos
      set t := (|dotProduct x0 α - α0| + 1) / dotProduct α y with ht_def
      have ht : 0 ≤ t := by positivity
      let x : Fin n → ℝ := x0 - t • y
      have hx : x ∈ {x : Fin n → ℝ | ∀ i, b i ≤ (A.mulVec x) i} := by
        intro i
        rw [hmv]
        have h1 := hgen i
        have h2 := hx0 i
        rw [hmv] at h2
        simp only [x, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        simp only [mul_zero, add_zero] at h1
        nlinarith
      have hv := hval x hx
      have e : dotProduct x α = dotProduct x0 α - t * dotProduct α y := by
        simp only [x, sub_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm y α]
      have e2 : t * dotProduct α y = |dotProduct x0 α - α0| + 1 := by
        rw [ht_def, div_mul_cancel₀ _ hαy.ne']
      have := le_abs_self (dotProduct x0 α - α0)
      linarith

end P2MFarkasDE

namespace P2MVPolyDE

lemma ray_nonneg (a b c : ℝ) (h : ∀ μ : ℝ, 0 ≤ μ → c ≤ a + μ * b) : 0 ≤ b := by
  by_contra hb
  push_neg at hb
  have hnb : 0 < -b := by linarith
  have hμ : 0 ≤ (|a - c| + 1) / (-b) := by positivity
  have h1 := h _ hμ
  have e : (|a - c| + 1) / (-b) * b = -(|a - c| + 1) := by
    have hb0 : b ≠ 0 := hb.ne
    field_simp
    try ring
  have := le_abs_self (a - c)
  linarith

end P2MVPolyDE

open Disjunctive.VPolyhedral in
theorem solution {n : ℕ} {Q : Type*} [Fintype Q] [Nonempty Q]
    {Rh : Q → ℕ}
    (Vidx Ridx : Q → Type*) [∀ h, Fintype (Vidx h)] [∀ h, Fintype (Ridx h)]
    [∀ h, Nonempty (Vidx h)]
    (vpt : ∀ h, Vidx h → Fin n → ℝ) (rvec : ∀ h, Ridx h → Fin n → ℝ)
    (Dtil : ∀ h, Matrix (Fin (Rh h)) (Fin n) ℝ) (d0til : ∀ h, Fin (Rh h) → ℝ)
    (hDesc : ∀ h, {x : Fin n → ℝ | ∀ i, d0til h i ≤ ((Dtil h).mulVec x) i} =
      {x : Fin n → ℝ | ∃ (lam : Vidx h → ℝ) (mu : Ridx h → ℝ), 0 ≤ lam ∧ 0 ≤ mu ∧
        ∑ p, lam p = 1 ∧ x = (∑ p, lam p • vpt h p) + ∑ r, mu r • rvec h r})
    (P : Set (Fin n → ℝ)) (xbar : Fin n → ℝ) (hxbar : xbar ∈ P)
    (alpha : Fin n → ℝ) (beta : ℝ) (hviol : dotProduct alpha xbar < beta) :
    IsVPolyhedralValid Vidx Ridx vpt rvec alpha beta ↔
      ∃ (t : ℝ) (u : ∀ h, Fin (Rh h) → ℝ), 0 < t ∧
        IsCGLP129Feasible Dtil d0til (t • alpha) u (t * beta) ∧
        IsGICFromS Dtil d0til P u (t • alpha) (t * beta) := by
  classical
  -- membership of `vpt h p0 + μ • rvec h r` (μ ≥ 0) in the relaxed disjunct
  have memray : ∀ h (p0 : Vidx h) (r : Ridx h) (μ : ℝ), 0 ≤ μ →
      ∀ i, d0til h i ≤ ((Dtil h).mulVec (vpt h p0 + μ • rvec h r)) i := by
    intro h p0 r μ hμ
    have hm : vpt h p0 + μ • rvec h r ∈
        {x : Fin n → ℝ | ∃ (lam : Vidx h → ℝ) (mu : Ridx h → ℝ), 0 ≤ lam ∧ 0 ≤ mu ∧
          ∑ p, lam p = 1 ∧ x = (∑ p, lam p • vpt h p) + ∑ r, mu r • rvec h r} := by
      refine ⟨fun q => if q = p0 then 1 else 0, fun s => if s = r then μ else 0, ?_, ?_, ?_, ?_⟩
      · intro q; by_cases hq : q = p0 <;> simp [hq]
      · intro s; by_cases hs : s = r <;> simp [hs, hμ]
      · simp
      · simp [ite_smul]
    rw [← hDesc h] at hm
    exact hm
  have memvert : ∀ h (p0 : Vidx h), ∀ i, d0til h i ≤ ((Dtil h).mulVec (vpt h p0)) i := by
    intro h p0
    have hm : vpt h p0 ∈
        {x : Fin n → ℝ | ∃ (lam : Vidx h → ℝ) (mu : Ridx h → ℝ), 0 ≤ lam ∧ 0 ≤ mu ∧
          ∑ p, lam p = 1 ∧ x = (∑ p, lam p • vpt h p) + ∑ r, mu r • rvec h r} := by
      refine ⟨fun q => if q = p0 then 1 else 0, 0, ?_, le_rfl, ?_, ?_⟩
      · intro q; by_cases hq : q = p0 <;> simp [hq]
      · simp
      · simp [ite_smul]
    rw [← hDesc h] at hm
    exact hm
  constructor
  · rintro ⟨hV, hR⟩
    have key : ∀ h : Q, ∃ v : Fin (Rh h) → ℝ, Matrix.vecMul v (Dtil h) = alpha ∧
        beta ≤ dotProduct v (d0til h) ∧ 0 ≤ v := by
      intro h
      obtain ⟨p0⟩ := (inferInstance : Nonempty (Vidx h))
      refine P2MFarkasDE.affine_farkas (Dtil h) (d0til h) alpha beta ⟨vpt h p0, ?_⟩ ?_
      · exact memvert h p0
      · intro x hx
        have hx' : x ∈ {x : Fin n → ℝ | ∃ (lam : Vidx h → ℝ) (mu : Ridx h → ℝ), 0 ≤ lam ∧ 0 ≤ mu ∧
            ∑ p, lam p = 1 ∧ x = (∑ p, lam p • vpt h p) + ∑ r, mu r • rvec h r} := by
          rw [← hDesc h]; exact hx
        obtain ⟨lam, mu, hlam, hmu, hsum, rfl⟩ := hx'
        rw [dotProduct_comm, dotProduct_add, dotProduct_sum, dotProduct_sum]
        simp only [dotProduct_smul, smul_eq_mul]
        have h1 : ∑ p, lam p * beta ≤ ∑ p, lam p * dotProduct alpha (vpt h p) :=
          Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hV h p) (hlam p)
        have h2 : 0 ≤ ∑ r, mu r * dotProduct alpha (rvec h r) :=
          Finset.sum_nonneg fun r _ => mul_nonneg (hmu r) (hR h r)
        rw [← Finset.sum_mul, hsum, one_mul] at h1
        linarith
    choose v hv using key
    set S := ∑ h, ∑ i, v h i with hSdef
    have hinner : ∀ h, 0 ≤ ∑ i, v h i := fun h => Finset.sum_nonneg fun i _ => (hv h).2.2 i
    have hSpos : 0 < S := by
      rcases (Finset.sum_nonneg fun h _ => hinner h : (0:ℝ) ≤ S).lt_or_eq with hS | hS
      · exact hS
      exfalso
      have h0 : Q := Classical.arbitrary Q
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun h _ => hinner h)).mp hS.symm h0
        (Finset.mem_univ _)
      have h2 : v h0 = 0 := by
        funext i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => (hv h0).2.2 i)).mp h1 i
          (Finset.mem_univ _)
      obtain ⟨ha, hb, -⟩ := hv h0
      rw [h2] at ha hb
      simp at ha hb
      rw [← ha] at hviol
      simp at hviol
      linarith
    have hSi : 0 ≤ S⁻¹ := inv_nonneg.mpr hSpos.le
    refine ⟨S⁻¹, fun h => S⁻¹ • v h, inv_pos.mpr hSpos,
      ⟨fun h => ?_, fun h => ?_, ?_, fun h i => ?_⟩, ?_, xbar, hxbar, ?_⟩
    · rw [Matrix.smul_vecMul, (hv h).1]
    · rw [smul_dotProduct, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hv h).2.1 hSi
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      exact inv_mul_cancel₀ hSpos.ne'
    · exact mul_nonneg hSi ((hv h).2.2 i)
    · intro x _ hnot
      push_neg at hnot
      obtain ⟨h, hh⟩ := hnot
      calc S⁻¹ * beta ≤ dotProduct (S⁻¹ • v h) (d0til h) := by
            rw [smul_dotProduct, smul_eq_mul]
            exact mul_le_mul_of_nonneg_left (hv h).2.1 hSi
        _ ≤ dotProduct (S⁻¹ • v h) ((Dtil h).mulVec x) := hh
        _ = dotProduct (S⁻¹ • alpha) x := by
            rw [Matrix.dotProduct_mulVec, Matrix.smul_vecMul, (hv h).1]
    · rw [smul_dotProduct, smul_eq_mul]
      exact mul_lt_mul_of_pos_left hviol (inv_pos.mpr hSpos)
  · rintro ⟨t, u, ht, ⟨hα, hβ, -, hnn⟩, -⟩
    -- core inequality for points of the relaxed disjunct
    have core : ∀ h (x : Fin n → ℝ), (∀ i, d0til h i ≤ ((Dtil h).mulVec x) i) →
        t * beta ≤ t * dotProduct alpha x := by
      intro h x hx
      calc t * beta ≤ dotProduct (u h) (d0til h) := hβ h
        _ ≤ dotProduct (u h) ((Dtil h).mulVec x) :=
            dotProduct_le_dotProduct_of_nonneg_left hx (hnn h)
        _ = dotProduct (t • alpha) x := by rw [Matrix.dotProduct_mulVec, ← hα h]
        _ = t * dotProduct alpha x := by rw [smul_dotProduct, smul_eq_mul]
    refine ⟨fun h p => ?_, fun h r => ?_⟩
    · have := core h (vpt h p) (memvert h p)
      exact le_of_mul_le_mul_left this ht
    · obtain ⟨p0⟩ := (inferInstance : Nonempty (Vidx h))
      refine P2MVPolyDE.ray_nonneg (dotProduct alpha (vpt h p0)) _ beta fun μ hμ => ?_
      have := le_of_mul_le_mul_left (core h _ (memray h p0 r μ hμ)) ht
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at this
      exact this
