-- Prove2me | solution 1 for BFFPyramidal.lemma_III
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-13T19:18:08.040423+00:00
-- url     : https://prove2.me/submissions/ff6a89f4-9e00-48c9-bfec-beeca41b6f91

import Mathlib
import Definitions.Def_BFFPyramidal_pyramidal
import Definitions.Def_BFFPyramidal_arithmetic

open BFFPyramidal

universe u

/-! ### Arithmetic of the greatest prime factor -/

private lemma le_maxPrimeFac {m r : ℕ} (h : r ∈ m.primeFactors) : r ≤ maxPrimeFac m :=
  Finset.le_sup (f := id) h

private lemma maxPrimeFac_le_of_subset {m k : ℕ} (h : m.primeFactors ⊆ k.primeFactors) :
    maxPrimeFac m ≤ maxPrimeFac k := by
  exact Finset.sup_mono h

private lemma maxPrimeFac_mem {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) :
    maxPrimeFac m ∈ m.primeFactors := by
  have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨r, hr, hsup⟩ := Finset.exists_mem_eq_sup m.primeFactors hne id
  have h2 : maxPrimeFac m = r := hsup
  rw [h2]; exact hr

private lemma maxPrimeFac_prime {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : (maxPrimeFac m).Prime :=
  (Nat.mem_primeFactors.mp (maxPrimeFac_mem h0 h1)).1

/-! ### Pyramidality is inherited by the first term of the chain -/

private lemma isPyramidal_sub {G : Type u} [Group G] [Finite G] {n : ℕ} {c : ℕ → Subgroup G}
    (hn1 : 1 ≤ n) (hbot : c n = ⊥)
    (hstep : ∀ k < n, c (k + 1) ≤ c k ∧
      Subgroup.relIndex (c (k + 1)) (c k) = Nat.minFac (Nat.card (c k))) :
    IsPyramidal (c 1) := by
  have hmono : ∀ d j : ℕ, j + d ≤ n → c (j + d) ≤ c j := by
    intro d
    induction d with
    | zero => intro j _; simp
    | succ d ih =>
      intro j hj
      rw [show j + (d + 1) = (j + d) + 1 by omega]
      exact le_trans (hstep (j + d) (by omega)).1 (ih j (by omega))
  have hle1 : ∀ k : ℕ, 1 ≤ k → k ≤ n → c k ≤ c 1 := by
    intro k hk1 hkn
    have h := hmono (k - 1) 1 (by omega)
    rwa [show 1 + (k - 1) = k by omega] at h
  refine ⟨n - 1, fun k => (c (k + 1)).subgroupOf (c 1), ?_, ?_, ?_⟩
  · show (c 1).subgroupOf (c 1) = ⊤
    exact Subgroup.subgroupOf_self (c 1)
  · show (c (n - 1 + 1)).subgroupOf (c 1) = ⊥
    rw [show n - 1 + 1 = n by omega, hbot, Subgroup.bot_subgroupOf]
  · intro k hk
    obtain ⟨hle, hidx⟩ := hstep (k + 1) (by omega)
    have hsub1 : c (k + 1) ≤ c 1 := hle1 (k + 1) (by omega) (by omega)
    refine ⟨Subgroup.comap_mono hle, ?_⟩
    have hc : Nat.card ((c (k + 1)).subgroupOf (c 1)) = Nat.card (c (k + 1)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsub1).toEquiv
    rw [Subgroup.relIndex_subgroupOf hsub1, hc]
    exact hidx

/-! ### The inductive heart of Lemma III -/

private lemma key : ∀ (N : ℕ) (G : Type u) [Group G] [Finite G],
    Nat.card G < N → IsPyramidal G →
    ∃ S : Subgroup G, S.Normal ∧ IsPGroup (maxPrimeFac (Nat.card G)) S ∧
      ¬ (maxPrimeFac (Nat.card G) ∣ S.index) := by
  intro N
  induction N with
  | zero => intro G _ _ hlt _; exact absurd hlt (Nat.not_lt_zero _)
  | succ N ih =>
    intro G _ _ hlt hG
    by_cases h1 : Nat.card G = 1
    · have hq0 : maxPrimeFac (Nat.card G) = 0 := by simp [maxPrimeFac, h1]
      refine ⟨⊤, inferInstance, ?_, ?_⟩
      · rw [hq0]; exact IsPGroup.zero _
      · rw [hq0, Subgroup.index_top]; simp
    have hc0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have hpp : (Nat.minFac (Nat.card G)).Prime := Nat.minFac_prime h1
    have hqp : (maxPrimeFac (Nat.card G)).Prime := maxPrimeFac_prime hc0 h1
    have hple : Nat.minFac (Nat.card G) ≤ maxPrimeFac (Nat.card G) :=
      le_maxPrimeFac (Nat.mem_primeFactors.mpr ⟨hpp, Nat.minFac_dvd _, hc0⟩)
    rcases eq_or_lt_of_le hple with hpe | hplt
    · -- `G` is a `q`-group: take the whole group
      refine ⟨⊤, inferInstance, ?_, ?_⟩
      · refine IsPGroup.of_card (n := (Nat.card G).primeFactorsList.length) ?_
        rw [Subgroup.card_top]
        refine Nat.eq_prime_pow_of_unique_prime_dvd hc0 ?_
        intro d hd hdvd
        have h2 : Nat.minFac (Nat.card G) ≤ d := Nat.minFac_le_of_dvd hd.two_le hdvd
        have h3 : d ≤ maxPrimeFac (Nat.card G) :=
          le_maxPrimeFac (Nat.mem_primeFactors.mpr ⟨hd, hdvd, hc0⟩)
        omega
      · rw [Subgroup.index_top]; exact hqp.not_dvd_one
    -- main case : `p(|G|) < P(|G|)`
    obtain ⟨n, c, h0, hn, hstep⟩ := hG
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · refine absurd ?_ h1
        calc Nat.card G = Nat.card (⊤ : Subgroup G) := Subgroup.card_top.symm
          _ = Nat.card (⊥ : Subgroup G) := by rw [← h0, hn]
          _ = 1 := Subgroup.card_bot
      · exact hpos
    have hidx1 : (c 1).index = Nat.minFac (Nat.card G) := by
      obtain ⟨_, hidx⟩ := hstep 0 (by omega)
      rw [h0, Subgroup.relIndex_top_right, Subgroup.card_top] at hidx
      exact hidx
    have hnorm1 : (c 1).Normal := Subgroup.normal_of_index_eq_minFac_card hidx1
    have hcardG : Nat.card (c 1) * Nat.minFac (Nat.card G) = Nat.card G := by
      rw [← hidx1]; exact Subgroup.card_mul_index (c 1)
    have hc1 : Nat.card (c 1) ≠ 0 := Nat.card_pos.ne'
    have hpf : (Nat.card G).primeFactors
        = (Nat.card (c 1)).primeFactors ∪ {Nat.minFac (Nat.card G)} := by
      have h := Nat.primeFactors_mul hc1 hpp.ne_zero
      rw [hcardG] at h
      rw [h, hpp.primeFactors]
    have hqne : maxPrimeFac (Nat.card G) ≠ Nat.minFac (Nat.card G) := by omega
    have hqmem : maxPrimeFac (Nat.card G) ∈ (Nat.card (c 1)).primeFactors := by
      have h := maxPrimeFac_mem hc0 h1
      rw [hpf, Finset.mem_union, Finset.mem_singleton] at h
      tauto
    have hqq : maxPrimeFac (Nat.card (c 1)) = maxPrimeFac (Nat.card G) :=
      le_antisymm (maxPrimeFac_le_of_subset (by rw [hpf]; exact Finset.subset_union_left))
        (le_maxPrimeFac hqmem)
    have hlt1 : Nat.card (c 1) < N := by
      have hpos : 0 < Nat.card (c 1) := Nat.card_pos
      have h2 : Nat.card (c 1) * 2 ≤ Nat.card G :=
        le_trans (Nat.mul_le_mul (le_refl _) hpp.two_le) (le_of_eq hcardG)
      omega
    obtain ⟨S₁, hS₁n, hS₁p, hS₁i⟩ := ih ↥(c 1) hlt1 (isPyramidal_sub hn1 hn hstep)
    rw [hqq] at hS₁p hS₁i
    have : Fact (maxPrimeFac (Nat.card G)).Prime := ⟨hqp⟩
    have hchar : S₁.Characteristic :=
      Sylow.characteristic_of_normal (hS₁p.toSylow hS₁i) hS₁n
    refine ⟨S₁.map (c 1).subtype, inferInstance, hS₁p.map (c 1).subtype, ?_⟩
    rw [Subgroup.index_map_subtype, hidx1]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hqp).mp hdvd with h | h
    · exact hS₁i h
    · exact hqne ((Nat.prime_dvd_prime_iff_eq hqp hpp).mp h)

/-! ### Lemma III -/

theorem solution {G : Type*} [Group G] [Finite G] (hG : IsPyramidal G) :
    Subsingleton (Sylow (maxPrimeFac (Nat.card G)) G) ∧
      ∀ S : Sylow (maxPrimeFac (Nat.card G)) G, (S : Subgroup G).Normal := by
  have hss : Subsingleton (Sylow (maxPrimeFac (Nat.card G)) G) := by
    by_cases h1 : Nat.card G = 1
    · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
      have hall : ∀ H : Subgroup G, H = ⊤ := fun H =>
        le_antisymm le_top fun x _ => by rw [Subsingleton.elim x 1]; exact H.one_mem
      exact ⟨fun P Q => Sylow.ext (by rw [hall (P : Subgroup G), hall (Q : Subgroup G)])⟩
    · obtain ⟨S, hn, hp, hi⟩ := key (Nat.card G + 1) G (by omega) hG
      have : Fact (maxPrimeFac (Nat.card G)).Prime := ⟨maxPrimeFac_prime Nat.card_pos.ne' h1⟩
      exact @Unique.instSubsingleton _ (Sylow.unique_of_normal (hp.toSylow hi) hn)
  exact ⟨hss, fun S => Sylow.normal_of_subsingleton S⟩

#print axioms solution
#check @solution
