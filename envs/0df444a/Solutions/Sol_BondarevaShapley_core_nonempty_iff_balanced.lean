-- Prove2me | solution 1 for BondarevaShapley.core_nonempty_iff_balanced
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:37:57.045102+00:00
-- url     : https://prove2.me/submissions/d2577ed2-c381-4efe-8733-5c6cba03346a

import Mathlib

set_option autoImplicit false

namespace BSHelp

open Finset
open scoped Pointwise

variable {N : Type*} [Fintype N] [DecidableEq N]

lemma forward (v : Finset N → ℝ) (x : N → ℝ) (hx1 : ∑ i, x i = v univ)
    (hx2 : ∀ S : Finset N, v S ≤ ∑ i ∈ S, x i)
    (B : Finset (Finset N)) (δ : Finset N → ℝ) (hδ : ∀ S ∈ B, 0 < δ S)
    (hbal : ∀ i : N, ∑ S ∈ B.filter (fun S => i ∈ S), δ S = 1) :
    ∑ S ∈ B, δ S * v S ≤ v univ := by
  calc ∑ S ∈ B, δ S * v S ≤ ∑ S ∈ B, δ S * ∑ i ∈ S, x i :=
        Finset.sum_le_sum (fun S hS => mul_le_mul_of_nonneg_left (hx2 S) (hδ S hS).le)
    _ = ∑ S ∈ B, ∑ i, if i ∈ S then δ S * x i else 0 := by
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [Finset.mul_sum, ← Finset.sum_filter]
        congr 1
        ext i
        simp
    _ = ∑ i, x i * ∑ S ∈ B.filter (fun S => i ∈ S), δ S := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        split_ifs <;> ring
    _ = v univ := by simp [hbal, hx1]

noncomputable def gen (v : Finset N → ℝ) (S : Finset N) : (N → ℝ) × ℝ :=
  (((S.card : ℝ)⁻¹) • (fun i => if i ∈ S then (1:ℝ) else 0), v S / S.card)

noncomputable def Lmap (v : Finset N → ℝ) : (Finset N → ℝ) →ₗ[ℝ] (N → ℝ) × ℝ where
  toFun l := ∑ S, l S • gen v S
  map_add' l m := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c l := by simp [Finset.smul_sum, mul_smul]

lemma not_mem_T [Nonempty N] (v : Finset N → ℝ)
    (hbal : ∀ (B : Finset (Finset N)) (δ : Finset N → ℝ),
        ∅ ∉ B → (∀ S ∈ B, 0 < δ S) →
        (∀ i : N, ∑ S ∈ B.filter (fun S => i ∈ S), δ S = 1) →
        ∑ S ∈ B, δ S * v S ≤ v Finset.univ)
    (ε : ℝ) (hε : 0 < ε) :
    (((Fintype.card N : ℝ)⁻¹) • (fun _ => (1:ℝ)), v univ / Fintype.card N + ε) ∉
      (Lmap v '' stdSimplex ℝ (Finset N)) + (({0} : Set (N → ℝ)) ×ˢ Set.Iic (0:ℝ)) := by
  rintro ⟨k, ⟨l, hl, rfl⟩, r, ⟨hr1, hr2⟩, hq⟩
  have hn : (0:ℝ) < Fintype.card N := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card N : ℝ) with hn_def
  have hr1' : r.1 = 0 := hr1
  have hr2' : r.2 ≤ 0 := hr2
  have h1 : ∀ i, n⁻¹ = ∑ S, l S * ((S.card:ℝ)⁻¹ * if i ∈ S then 1 else 0) := by
    intro i
    have := congrArg (fun p => p.1 i) hq
    simp [Lmap, gen, Prod.fst_sum, Finset.sum_apply, hr1'] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    split_ifs <;> simp
  have h2 : v univ / n + ε = ∑ S, l S * (v S / S.card) + r.2 := by
    have := congrArg (fun p => p.2) hq
    simp [Lmap, gen, Prod.snd_sum] at this
    rw [← this]
  have hl0 : ∀ S, 0 ≤ l S := hl.1
  have key := hbal (univ.filter (fun S : Finset N => S.Nonempty ∧ 0 < l S))
    (fun S => n * l S / S.card) (by simp) ?_ ?_
  · have e : ∑ S ∈ univ.filter (fun S : Finset N => S.Nonempty ∧ 0 < l S),
        n * l S / S.card * v S = n * ∑ S, l S * (v S / S.card) := by
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      split_ifs with h
      · ring
      · rcases S.eq_empty_or_nonempty with hS | hS
        · simp [hS]
        · have : l S = 0 := le_antisymm (not_lt.mp (fun h' => h ⟨hS, h'⟩)) (hl0 S)
          simp [this]
    rw [e] at key
    have : ∑ S, l S * (v S / S.card) = v univ / n + ε - r.2 := by linarith
    rw [this] at key
    have : n * (v univ / n + ε - r.2) = v univ + n * ε - n * r.2 := by
      field_simp
    nlinarith
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    have : (0:ℝ) < S.card := by exact_mod_cast hS.1.card_pos
    exact div_pos (mul_pos hn hS.2) this
  · intro i
    rw [Finset.filter_filter, Finset.sum_filter]
    calc (∑ S, if (S.Nonempty ∧ 0 < l S) ∧ i ∈ S then n * l S / S.card else 0)
        = n * ∑ S, l S * ((S.card:ℝ)⁻¹ * if i ∈ S then 1 else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun S _ => ?_)
          by_cases hiS : i ∈ S
          · by_cases hlS : 0 < l S
            · have hne : S.Nonempty := ⟨i, hiS⟩
              simp [hiS, hlS, hne]
              ring
            · have : l S = 0 := le_antisymm (not_lt.mp hlS) (hl0 S)
              simp [this]
          · simp [hiS]
      _ = n * n⁻¹ := by rw [← h1 i]
      _ = 1 := mul_inv_cancel₀ hn.ne'

lemma approx [Nonempty N] (v : Finset N → ℝ) (hv : v ∅ = 0)
    (hbal : ∀ (B : Finset (Finset N)) (δ : Finset N → ℝ),
        ∅ ∉ B → (∀ S ∈ B, 0 < δ S) →
        (∀ i : N, ∑ S ∈ B.filter (fun S => i ∈ S), δ S = 1) →
        ∑ S ∈ B, δ S * v S ≤ v Finset.univ)
    (η : ℝ) (hη : 0 < η) :
    ∃ x : N → ℝ, ∑ i, x i = v univ ∧ ∀ S : Finset N, v S ≤ ∑ i ∈ S, x i + η := by
  have hn : (0:ℝ) < Fintype.card N := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card N : ℝ) with hn_def
  set ε := η / n with hε_def
  have hε : 0 < ε := div_pos hη hn
  have hKc : IsCompact (Lmap v '' stdSimplex ℝ (Finset N)) :=
    (isCompact_stdSimplex ℝ (Finset N)).image (LinearMap.continuous_of_finiteDimensional _)
  have hTcl : IsClosed ((Lmap v '' stdSimplex ℝ (Finset N)) +
      (({0} : Set (N → ℝ)) ×ˢ Set.Iic (0:ℝ))) :=
    (isClosed_singleton.prod isClosed_Iic).add_left_of_isCompact hKc
  have hTcv : Convex ℝ ((Lmap v '' stdSimplex ℝ (Finset N)) +
      (({0} : Set (N → ℝ)) ×ˢ Set.Iic (0:ℝ))) :=
    ((convex_stdSimplex ℝ _).linear_image _).add ((convex_singleton _).prod (convex_Iic _))
  obtain ⟨f, u, hfq, hfT⟩ := geometric_hahn_banach_point_closed hTcv hTcl
    (not_mem_T v hbal ε hε)
  set a : N → ℝ := fun i => f (Pi.single i 1, 0) with ha_def
  set b : ℝ := f (0, 1) with hb_def
  have hf : ∀ (z : N → ℝ) (w : ℝ), f (z, w) = ∑ i, z i * a i + w * b := by
    intro z w
    have : ((z, w) : (N → ℝ) × ℝ) =
        ∑ i, z i • ((Pi.single i 1 : N → ℝ), (0:ℝ)) + w • ((0 : N → ℝ), (1:ℝ)) := by
      ext j
      · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    rw [this, map_add, map_sum, map_smul, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, smul_eq_mul]
  have hmem : ∀ S : Finset N, ∀ t : ℝ, 0 ≤ t → u < f (gen v S) - t * b := by
    intro S t ht
    have hm : gen v S + ((0 : N → ℝ), -t) ∈ (Lmap v '' stdSimplex ℝ (Finset N)) +
        (({0} : Set (N → ℝ)) ×ˢ Set.Iic (0:ℝ)) := by
      refine Set.add_mem_add ⟨Pi.single S 1, single_mem_stdSimplex ℝ S, ?_⟩ ⟨rfl, ?_⟩
      · simp [Lmap, Pi.single_apply]
      · simp [ht]
    have := hfT _ hm
    rw [map_add, hf 0 (-t)] at this
    simpa [sub_eq_add_neg] using this
  have hgen : ∀ S : Finset N, f (gen v S) =
      (S.card : ℝ)⁻¹ * ∑ i ∈ S, a i + v S / S.card * b := by
    intro S
    rw [gen, hf]
    congr 1
    simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.mul_sum]
    congr 1
    ext i
    simp
  have hfq' : f (((Fintype.card N : ℝ)⁻¹) • (fun _ => (1:ℝ)), v univ / Fintype.card N + ε)
      = n⁻¹ * ∑ i, a i + (v univ / n + ε) * b := by
    rw [hf]
    simp [Finset.mul_sum, hn_def]
  rw [hfq'] at hfq
  -- b ≤ 0
  have hb0 : b ≤ 0 := by
    by_contra hb
    push Not at hb
    have h0 := hmem ∅ 0 le_rfl
    have hgen0 : f (gen v ∅) = 0 := by rw [hgen]; simp
    rw [hgen0] at h0
    have h1 := hmem ∅ (-u / b) (div_nonneg (by linarith) hb.le)
    rw [hgen0, div_mul_cancel₀ _ hb.ne'] at h1
    linarith
  rcases hb0.lt_or_eq with hb | hb
  · refine ⟨fun i => a i / (-b) - ((∑ j, a j) / (-b) - v univ) / n, ?_, ?_⟩
    · rw [Finset.sum_sub_distrib, ← Finset.sum_div]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← hn_def]
      field_simp
      ring
    · intro S
      rcases S.eq_empty_or_nonempty with hS | hS
      · subst hS
        simp [hv, hη.le]
      have hs : (0:ℝ) < S.card := by exact_mod_cast hS.card_pos
      have hsn : (S.card : ℝ) ≤ n := by rw [hn_def]; exact_mod_cast Finset.card_le_univ S
      have hS1 := hmem S 0 le_rfl
      rw [hgen] at hS1
      have hlt : n⁻¹ * ∑ i, a i + (v univ / n + ε) * b <
          (S.card : ℝ)⁻¹ * ∑ i ∈ S, a i + v S / S.card * b := by linarith
      have K := mul_lt_mul_of_pos_left hlt hs
      have e1 : (S.card : ℝ) * ((S.card : ℝ)⁻¹ * ∑ i ∈ S, a i + v S / S.card * b) =
          ∑ i ∈ S, a i + v S * b := by
        have hss : (S.card : ℝ) * (S.card : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hs.ne'
        calc (S.card : ℝ) * ((S.card : ℝ)⁻¹ * ∑ i ∈ S, a i + v S / S.card * b)
            = ((S.card : ℝ) * (S.card : ℝ)⁻¹) * ∑ i ∈ S, a i
              + ((S.card : ℝ) * (S.card : ℝ)⁻¹) * v S * b := by ring
          _ = ∑ i ∈ S, a i + v S * b := by rw [hss]; ring
      rw [e1] at K
      rw [Finset.sum_sub_distrib, ← Finset.sum_div]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hβ : 0 < -b := by linarith
      set P := ∑ i ∈ S, a i
      set Q := ∑ i, a i
      set s := (S.card : ℝ)
      have K2 : (v S - s * v univ / n - s * ε) * (-b) < P - s * Q / n := by
        have : s * (n⁻¹ * Q + (v univ / n + ε) * b) =
            s * Q / n + s * v univ * b / n + s * ε * b := by ring
        rw [this] at K
        have e : (P - s * Q / n) - (v S - s * v univ / n - s * ε) * (-b) =
            (P + v S * b) - (s * Q / n + s * v univ * b / n + s * ε * b) := by ring
        exact sub_pos.mp (by rw [e]; exact sub_pos.mpr K)
      have K3 : v S - s * v univ / n - s * ε < (P - s * Q / n) / (-b) := by
        rw [lt_div_iff₀ hβ]; exact K2
      have e2 : P / (-b) - s * ((Q / (-b) - v univ) / n) =
          (P - s * Q / n) / (-b) + s * v univ / n := by
        field_simp
        ring
      rw [e2]
      have : s * ε ≤ η := by
        rw [hε_def]
        calc s * (η / n) ≤ n * (η / n) := by gcongr
          _ = η := by field_simp
      linarith
  · exfalso
    have h := hmem univ 0 le_rfl
    rw [hgen, Finset.card_univ, ← hn_def, hb] at h
    rw [hb] at hfq
    simp at h hfq
    linarith

lemma exists_core [Nonempty N] (v : Finset N → ℝ) (hv : v ∅ = 0)
    (hbal : ∀ (B : Finset (Finset N)) (δ : Finset N → ℝ),
        ∅ ∉ B → (∀ S ∈ B, 0 < δ S) →
        (∀ i : N, ∑ S ∈ B.filter (fun S => i ∈ S), δ S = 1) →
        ∑ S ∈ B, δ S * v S ≤ v Finset.univ) :
    ∃ x : N → ℝ, ∑ i, x i = v univ ∧ ∀ S : Finset N, v S ≤ ∑ i ∈ S, x i := by
  let t : ℕ → Set (N → ℝ) := fun k =>
    {x | ∑ i, x i = v univ ∧ ∀ S : Finset N, v S ≤ ∑ i ∈ S, x i + 1 / ((k:ℝ) + 1)}
  have hcont : ∀ S : Finset N, Continuous (fun x : N → ℝ => ∑ i ∈ S, x i) :=
    fun S => continuous_finsetSum _ (fun i _ => continuous_apply i)
  have htd : ∀ k, t (k+1) ⊆ t k := by
    intro k x hx
    obtain ⟨h1, h2⟩ := hx
    refine ⟨h1, fun S => (h2 S).trans ?_⟩
    have : 1 / (((k + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((k:ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast; linarith
    linarith
  have htn : ∀ k, (t k).Nonempty := fun k => approx v hv hbal _ (by positivity)
  have htcl : ∀ k, IsClosed (t k) := by
    intro k
    have e : t k = {x | ∑ i, x i = v univ} ∩
        ⋂ S : Finset N, {x | v S ≤ ∑ i ∈ S, x i + 1 / ((k:ℝ) + 1)} := by
      ext x
      simp [t, Set.mem_iInter]
    rw [e]
    exact (isClosed_eq (hcont univ) continuous_const).inter
      (isClosed_iInter fun S => isClosed_le continuous_const ((hcont S).add continuous_const))
  have ht0 : IsCompact (t 0) := by
    apply (isCompact_univ_pi (fun i => isCompact_Icc (a := v {i} - 1)
      (b := v univ - v (univ.erase i) + 1))).of_isClosed_subset (htcl 0)
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i
    have a1 := h2 {i}
    have a2 := h2 (univ.erase i)
    have a3 := Finset.add_sum_erase univ x (mem_univ i)
    simp only [Finset.sum_singleton, Nat.cast_zero, zero_add, ne_eq, one_ne_zero,
      not_false_eq_true, div_self] at a1 a2
    constructor <;> linarith
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn ht0 htcl
  simp only [Set.mem_iInter] at hx
  refine ⟨x, (hx 0).1, fun S => ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  exact ((hx k).2 S).trans (by linarith)

end BSHelp

theorem solution {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (v : Finset N → ℝ) (hv : v ∅ = 0) :
    (∃ x : N → ℝ, ∑ i, x i = v Finset.univ ∧ ∀ S : Finset N, v S ≤ ∑ i ∈ S, x i) ↔
      ∀ (B : Finset (Finset N)) (δ : Finset N → ℝ),
        ∅ ∉ B → (∀ S ∈ B, 0 < δ S) →
        (∀ i : N, ∑ S ∈ B.filter (fun S => i ∈ S), δ S = 1) →
        ∑ S ∈ B, δ S * v S ≤ v Finset.univ := by
  constructor
  · rintro ⟨x, hx1, hx2⟩ B δ _ hδ hbal
    exact BSHelp.forward v x hx1 hx2 B δ hδ hbal
  · intro hbal
    exact BSHelp.exists_core v hv hbal
