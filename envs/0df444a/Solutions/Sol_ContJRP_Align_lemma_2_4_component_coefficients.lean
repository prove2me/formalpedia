-- Prove2me | solution 1 for ContJRP.Align.lemma_2_4_component_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:22:54.81677+00:00
-- url     : https://prove2.me/submissions/a0e99be0-1478-4838-9462-4b59c1be97b1

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy
import Theorems.Thm_ContJRP_Align_observation_2_3_first_segment_active

open ContJRP.Align
open Classical

/-- For commensurable positive `x, y`, `alignMult x y · x = alignMult y x · y` (both sides are the
least common multiple). -/
theorem jrp24_alignMult (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℝ) * x = b * y) :
    (alignMult x y : ℝ) * x = (alignMult y x : ℝ) * y := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  have hne1 : {a : ℕ | 0 < a ∧ ∃ b : ℕ, 0 < b ∧ (a : ℝ) * x = b * y}.Nonempty :=
    ⟨a, ha, b, hb, hab⟩
  have hne2 : {b : ℕ | 0 < b ∧ ∃ a : ℕ, 0 < a ∧ (b : ℝ) * y = a * x}.Nonempty :=
    ⟨b, hb, a, ha, hab.symm⟩
  have h1 := Nat.sInf_mem hne1
  have h2 := Nat.sInf_mem hne2
  unfold alignMult
  set a0 := sInf {a : ℕ | 0 < a ∧ ∃ b : ℕ, 0 < b ∧ (a : ℝ) * x = b * y}
  set b0 := sInf {b : ℕ | 0 < b ∧ ∃ a : ℕ, 0 < a ∧ (b : ℝ) * y = a * x}
  obtain ⟨-, b1, hb1, e1⟩ := h1
  obtain ⟨-, a1, ha1, e2⟩ := h2
  have hle1 : a0 ≤ a1 := Nat.sInf_le ⟨ha1, b0, Nat.pos_of_ne_zero (by
    intro hz; rw [hz] at e2; simp at e2; rcases e2 with e2 | e2 <;> [omega; linarith]), e2.symm⟩
  have hle2 : b0 ≤ b1 := Nat.sInf_le ⟨hb1, a0, Nat.pos_of_ne_zero (by
    intro hz; rw [hz] at e1; simp at e1; rcases e1 with e1 | e1 <;> [omega; linarith]), e1.symm⟩
  have i1 : (a0 : ℝ) * x ≤ (b0 : ℝ) * y := by
    rw [e2]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle1) hx.le
  have i2 : (b0 : ℝ) * y ≤ (a0 : ℝ) * x := by
    rw [e1]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle2) hy.le
  linarith

theorem jrp24_alignMult_pos (x y : ℝ) (h : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (a : ℝ) * x = b * y) :
    0 < alignMult x y := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  have hne : {a : ℕ | 0 < a ∧ ∃ b : ℕ, 0 < b ∧ (a : ℝ) * x = b * y}.Nonempty :=
    ⟨a, ha, b, hb, hab⟩
  exact (Nat.sInf_mem hne).1

section comps
variable {n : ℕ} (ε Tt : ℝ) (Tstar : Fin n → ℝ) (Rstar : ℕ → ℝ)

theorem jrp24_comp_sub {C : Finset ℕ} (hC : C ∈ components ε Tt Tstar Rstar) :
    C ⊆ active ε Tt Tstar := by
  unfold components at hC
  obtain ⟨ℓ0, -, rfl⟩ := Finset.mem_image.mp hC
  exact Finset.filter_subset _ _

theorem jrp24_comp_eq {C : Finset ℕ} (hC : C ∈ components ε Tt Tstar Rstar) {ℓ : ℕ}
    (hℓ : ℓ ∈ C) : C = (active ε Tt Tstar).filter
      (fun ℓ' => (alignGraph ε Tt Tstar Rstar).Reachable ℓ ℓ') := by
  unfold components at hC
  obtain ⟨ℓ0, -, rfl⟩ := Finset.mem_image.mp hC
  rw [Finset.mem_filter] at hℓ
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hr⟩; exact ⟨hx, hℓ.2.symm.trans hr⟩
  · rintro ⟨hx, hr⟩; exact ⟨hx, hℓ.2.trans hr⟩

theorem jrp24_comp_reach {C : Finset ℕ} (hC : C ∈ components ε Tt Tstar Rstar) {ℓ₁ ℓ₂ : ℕ}
    (h1 : ℓ₁ ∈ C) (h2 : ℓ₂ ∈ C) : (alignGraph ε Tt Tstar Rstar).Reachable ℓ₁ ℓ₂ := by
  have := jrp24_comp_eq ε Tt Tstar Rstar hC h1
  rw [this, Finset.mem_filter] at h2
  exact h2.2

theorem jrp24_comp_unique {C C' : Finset ℕ} (hC : C ∈ components ε Tt Tstar Rstar)
    (hC' : C' ∈ components ε Tt Tstar Rstar) {ℓ : ℕ} (h : ℓ ∈ C) (h' : ℓ ∈ C') : C = C' := by
  rw [jrp24_comp_eq ε Tt Tstar Rstar hC h, jrp24_comp_eq ε Tt Tstar Rstar hC' h']

theorem jrp24_comp_of_mem {ℓ : ℕ} (hℓ : ℓ ∈ active ε Tt Tstar) :
    ∃ C ∈ components ε Tt Tstar Rstar, ℓ ∈ C := by
  refine ⟨_, Finset.mem_image_of_mem _ hℓ, ?_⟩
  rw [Finset.mem_filter]
  exact ⟨hℓ, SimpleGraph.Reachable.refl _⟩

theorem jrp24_comp_card : (components ε Tt Tstar Rstar).card ≤ (active ε Tt Tstar).card := by
  unfold components; exact Finset.card_image_le

end comps

theorem jrp24_alignMult_le (x y : ℝ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : (a : ℝ) * x = b * y) : alignMult x y ≤ a :=
  Nat.sInf_le ⟨ha, b, hb, hab⟩

theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    {n : ℕ} [NeZero n] (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (Tt : ℝ) (hTt1 : (1 - ε / 2) * tmin Tstar ≤ Tt) (hTt2 : Tt ≤ tmin Tstar)
    (Rstar : ℕ → ℝ) (hR : IsRepChoice ε Tt Tstar Rstar) :
    ∀ C ∈ components ε Tt Tstar Rstar, ∀ σ ∈ C, ∃ β : ℕ → ℝ,
      (∀ R : ℕ → ℝ, IsLPFeasibleOn ε Tt Tstar Rstar C R → ∀ ℓ ∈ C, R ℓ = β ℓ * R σ) ∧
      ∀ ℓ ∈ C, ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℝ) ≤ Psi ε ^ C.card ∧ (q : ℝ) ≤ Psi ε ^ C.card ∧
        β ℓ = (p : ℝ) / q := by
  intro C hC σ hσ
  set G := alignGraph ε Tt Tstar Rstar with hG
  set Ψ := Psi ε with hΨdef
  have hpos : ∀ ℓ ∈ active ε Tt Tstar, 0 < Rstar ℓ := by
    intro ℓ hℓ
    obtain ⟨i, hi, -⟩ := hR ℓ hℓ
    rw [hi]; exact hTstar i
  have hadj : ∀ b c, G.Adj b c →
      b ∈ active ε Tt Tstar ∧ c ∈ active ε Tt Tstar ∧
        ∃ p q : ℕ, 0 < p ∧ (p : ℝ) ≤ Ψ ∧ 0 < q ∧ (q : ℝ) ≤ Ψ ∧ (p : ℝ) * Rstar b = q * Rstar c := by
    intro b c h
    rw [hG] at h
    unfold alignGraph at h
    rw [SimpleGraph.fromRel_adj] at h
    obtain ⟨-, hr | hr⟩ := h
    · obtain ⟨h1, h2, a, b', ha, haΨ, hb, hbΨ, hab⟩ := hr
      exact ⟨h1, h2, a, b', ha, haΨ, hb, hbΨ, hab⟩
    · obtain ⟨h1, h2, a, b', ha, haΨ, hb, hbΨ, hab⟩ := hr
      exact ⟨h2, h1, b', a, hb, hbΨ, ha, haΨ, hab.symm⟩
  have hCsub := jrp24_comp_sub ε Tt Tstar Rstar hC
  have hCeq := jrp24_comp_eq ε Tt Tstar Rstar hC hσ
  have hσa := hCsub hσ
  have hRσ := hpos σ hσa
  refine ⟨fun ℓ => Rstar ℓ / Rstar σ, ?_, ?_⟩
  · -- part 1: propagation along edges
    intro R hfeas ℓ hℓ
    have key : ∀ c, Relation.ReflTransGen G.Adj σ c → R c * Rstar σ = R σ * Rstar c := by
      intro c hc
      induction hc with
      | refl => ring
      | tail hb hbc ih =>
        rename_i b c
        obtain ⟨hba, hca, p, q, hp, -, hq, -, hpq⟩ := hadj b c hbc
        have hbC : b ∈ C := by
          rw [hCeq, Finset.mem_filter]
          exact ⟨hba, (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hb⟩
        have hcC : c ∈ C := by
          rw [hCeq, Finset.mem_filter]
          exact ⟨hca, (SimpleGraph.reachable_iff_reflTransGen _ _).mpr (hb.tail hbc)⟩
        have hB := hfeas.2 b hbC c hcC hbc
        have hBs := jrp24_alignMult (Rstar b) (Rstar c) (hpos b hba) (hpos c hca)
          ⟨p, q, hp, hq, hpq⟩
        have hpos2 : (0 : ℝ) < alignMult (Rstar c) (Rstar b) := by
          exact_mod_cast jrp24_alignMult_pos (Rstar c) (Rstar b) ⟨q, p, hq, hp, hpq.symm⟩
        apply mul_left_cancel₀ hpos2.ne'
        calc (alignMult (Rstar c) (Rstar b) : ℝ) * (R c * Rstar σ)
            = ((alignMult (Rstar c) (Rstar b) : ℝ) * R c) * Rstar σ := by ring
          _ = ((alignMult (Rstar b) (Rstar c) : ℝ) * R b) * Rstar σ := by rw [hB]
          _ = (alignMult (Rstar b) (Rstar c) : ℝ) * (R b * Rstar σ) := by ring
          _ = (alignMult (Rstar b) (Rstar c) : ℝ) * (R σ * Rstar b) := by rw [ih]
          _ = R σ * ((alignMult (Rstar b) (Rstar c) : ℝ) * Rstar b) := by ring
          _ = R σ * ((alignMult (Rstar c) (Rstar b) : ℝ) * Rstar c) := by rw [hBs]
          _ = (alignMult (Rstar c) (Rstar b) : ℝ) * (R σ * Rstar c) := by ring
    have hreach : G.Reachable σ ℓ := by
      rw [hCeq, Finset.mem_filter] at hℓ; exact hℓ.2
    have := key ℓ ((SimpleGraph.reachable_iff_reflTransGen _ _).mp hreach)
    field_simp
    linarith
  · -- part 2: the ratio is a quotient of integers bounded by `Ψ ^ |C|`
    intro ℓ hℓ
    have hΨ1 : 1 ≤ Ψ := by
      have h0 := observation_2_3_first_segment_active ε hε0 hε1 Tstar hTstar Tt hTt1 hTt2
      have hL : 1 ≤ numSegments ε := by
        have : 0 ∈ Finset.range (numSegments ε) := Finset.mem_of_mem_filter _ h0
        simp at this; omega
      rw [hΨdef]; unfold Psi
      rw [le_div_iff₀ hε0]
      have hL1 : (1 : ℝ) ≤ (numSegments ε : ℝ) := by exact_mod_cast hL
      have hL2 : (1 : ℝ) ≤ (numSegments ε : ℝ) ^ 2 := by nlinarith
      have hp : (1 : ℝ) ≤ 2 ^ numSegments ε := one_le_pow₀ (by norm_num)
      nlinarith
    -- ratios along a walk
    have hwalk : ∀ (u v : ℕ) (w : G.Walk u v), u ∈ active ε Tt Tstar → v ∈ active ε Tt Tstar →
        ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (p : ℝ) ≤ Ψ ^ w.length ∧ (q : ℝ) ≤ Ψ ^ w.length ∧
          Rstar u / Rstar v = (p : ℝ) / q := by
      intro u v w
      induction w with
      | nil =>
        intro hu _
        refine ⟨1, 1, one_pos, one_pos, by simp, by simp, ?_⟩
        rw [div_self (hpos _ hu).ne']; simp
      | cons h w' ih =>
        rename_i u x v
        intro hu hv
        obtain ⟨-, hxa, a1, b1, ha1, ha1Ψ, hb1, hb1Ψ, hab1⟩ := hadj u x h
        obtain ⟨p, q, hp, hq, hpΨ, hqΨ, hpq⟩ := ih hxa hv
        have hBs := jrp24_alignMult (Rstar u) (Rstar x) (hpos u hu) (hpos x hxa)
          ⟨a1, b1, ha1, hb1, hab1⟩
        set α1 := alignMult (Rstar u) (Rstar x)
        set α2 := alignMult (Rstar x) (Rstar u)
        have hα1 : 0 < α1 := jrp24_alignMult_pos _ _ ⟨a1, b1, ha1, hb1, hab1⟩
        have hα2 : 0 < α2 := jrp24_alignMult_pos _ _ ⟨b1, a1, hb1, ha1, hab1.symm⟩
        have hα1Ψ : (α1 : ℝ) ≤ Ψ :=
          le_trans (by exact_mod_cast jrp24_alignMult_le _ _ a1 b1 ha1 hb1 hab1) ha1Ψ
        have hα2Ψ : (α2 : ℝ) ≤ Ψ :=
          le_trans (by exact_mod_cast jrp24_alignMult_le _ _ b1 a1 hb1 ha1 hab1.symm) hb1Ψ
        refine ⟨α2 * p, α1 * q, Nat.mul_pos hα2 hp, Nat.mul_pos hα1 hq, ?_, ?_, ?_⟩
        · rw [SimpleGraph.Walk.length_cons, pow_succ']
          push_cast
          exact mul_le_mul hα2Ψ hpΨ (Nat.cast_nonneg _) (by linarith)
        · rw [SimpleGraph.Walk.length_cons, pow_succ']
          push_cast
          exact mul_le_mul hα1Ψ hqΨ (Nat.cast_nonneg _) (by linarith)
        · have hu' := hpos u hu
          have hx' := hpos x hxa
          have hv' := hpos v hv
          have hα1' : (0 : ℝ) < α1 := by exact_mod_cast hα1
          have hq' : (0 : ℝ) < q := by exact_mod_cast hq
          rw [div_eq_div_iff hv'.ne' (by positivity)] at hpq ⊢
          push_cast
          -- Rstar u * (α1 q) = α1 Rstar u * q = α2 Rstar x * q = α2 (Rstar x q) = α2 p Rstar v
          calc Rstar u * ((α1 : ℝ) * q) = ((α1 : ℝ) * Rstar u) * q := by ring
            _ = ((α2 : ℝ) * Rstar x) * q := by rw [hBs]
            _ = (α2 : ℝ) * (Rstar x * q) := by ring
            _ = (α2 : ℝ) * (p * Rstar v) := by rw [hpq]
            _ = (α2 : ℝ) * p * Rstar v := by ring
    have hreach : G.Reachable ℓ σ := by
      rw [hCeq, Finset.mem_filter] at hℓ; exact hℓ.2.symm
    obtain ⟨w⟩ := hreach
    set w' := w.bypass with hw'
    have hpath : w'.IsPath := w.bypass_isPath
    -- the path stays inside `C`
    have hsupp : w'.support.toFinset ⊆ C := by
      intro x hx
      rw [List.mem_toFinset] at hx
      rw [hCeq, Finset.mem_filter]
      have hxσ : G.Reachable x σ := ⟨w'.dropUntil x hx⟩
      refine ⟨?_, hxσ.symm⟩
      cases hd : w'.dropUntil x hx with
      | nil => exact hσa
      | cons h _ => exact (hadj _ _ h).1
    have hlen : w'.length ≤ C.card := by
      have h1 := Finset.card_le_card hsupp
      rw [List.toFinset_card_of_nodup hpath.support_nodup, SimpleGraph.Walk.length_support] at h1
      omega
    have hℓa := hCsub hℓ
    obtain ⟨p, q, hp, hq, hpΨ, hqΨ, hpq⟩ := hwalk ℓ σ w' hℓa hσa
    exact ⟨p, q, hp, hq, le_trans hpΨ (pow_le_pow_right₀ hΨ1 hlen),
      le_trans hqΨ (pow_le_pow_right₀ hΨ1 hlen), hpq⟩
