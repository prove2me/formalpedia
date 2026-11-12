-- Prove2me | solution 1 for GenEmpLik.Expansion.eq_32
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T03:54:59.700383+00:00
-- url     : https://prove2.me/submissions/bb2976e1-2d7b-4aae-955b-4e847edd8d77

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_AssumptionA
import Definitions.Def_GenEmpLik_Expansion_robustMean
import Definitions.Def_GenEmpLik_Expansion_reparamSets
import Definitions.Def_VarianceRegularization_Expansion_empMean

open VarianceRegularization.Expansion

private lemma ereal_coe_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    ((∑ i ∈ s, g i : ℝ) : EReal) = ∑ i ∈ s, (g i : EReal) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j t hjt ih =>
    rw [Finset.sum_insert hjt, Finset.sum_insert hjt, EReal.coe_add, ih]

private lemma ereal_add_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) : x + y ≠ ⊥ := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | coe rx =>
    induction y using EReal.rec with
    | bot => exact absurd rfl hy
    | coe ry =>
      rw [← EReal.coe_add]
      exact EReal.coe_ne_bot _
    | top => simp
  | top =>
    induction y using EReal.rec with
    | bot => exact absurd rfl hy
    | coe ry => simp
    | top => simp

private lemma ereal_sum_ne_bot {ι : Type*} (s : Finset ι) (a : ι → EReal)
    (h : ∀ i ∈ s, a i ≠ ⊥) : ∑ i ∈ s, a i ≠ ⊥ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j t hjt ih =>
    rw [Finset.sum_insert hjt]
    exact ereal_add_ne_bot (h j (Finset.mem_insert_self j t))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

private lemma ereal_sum_eq_top_of_exists_top {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → EReal) (hbot : ∀ i ∈ s, a i ≠ ⊥)
    (htop : ∃ i ∈ s, a i = ⊤) : ∑ i ∈ s, a i = ⊤ := by
  rcases htop with ⟨i₀, hi₀, htop₀⟩
  rw [← Finset.add_sum_erase s a hi₀, htop₀]
  exact EReal.top_add_of_ne_bot
    (ereal_sum_ne_bot _ _ (fun i hi => hbot i (Finset.mem_of_mem_erase hi)))

private lemma ereal_pos_mul_sum_le_iff {n : ℕ} {c ρ : ℝ} (hc : 0 < c)
    (a : Fin n → EReal) (hbot : ∀ i, a i ≠ ⊥) :
    ∑ i, (c : EReal) * a i ≤ ((c * ρ : ℝ) : EReal) ↔ ∑ i, a i ≤ (ρ : EReal) := by
  have hmul_bot : ∀ i, (c : EReal) * a i ≠ ⊥ := by
    intro i
    rcases eq_top_or_lt_top (a i) with ht | hlt
    · rw [ht, EReal.coe_mul_top_of_pos hc]
      exact top_ne_bot
    · have hcoe : ((a i).toReal : EReal) = a i :=
        EReal.coe_toReal (ne_of_lt hlt) (hbot i)
      rw [← hcoe, ← EReal.coe_mul]
      exact EReal.coe_ne_bot _
  by_cases htop : ∃ i : Fin n, a i = ⊤
  · rcases htop with ⟨i₀, hi₀⟩
    have hsum1 : ∑ i, a i = ⊤ :=
      ereal_sum_eq_top_of_exists_top Finset.univ a (fun i _ => hbot i)
        ⟨i₀, Finset.mem_univ i₀, hi₀⟩
    have hsum2 : ∑ i, (c : EReal) * a i = ⊤ :=
      ereal_sum_eq_top_of_exists_top Finset.univ (fun i => (c : EReal) * a i)
        (fun i _ => hmul_bot i)
        ⟨i₀, Finset.mem_univ i₀, by rw [hi₀, EReal.coe_mul_top_of_pos hc]⟩
    rw [hsum1, hsum2, top_le_iff, top_le_iff]
    exact ⟨fun h => absurd h (EReal.coe_ne_top _), fun h => absurd h (EReal.coe_ne_top _)⟩
  · have htop' : ∀ i : Fin n, a i ≠ ⊤ := not_exists.mp htop
    have hcoe : ∀ i, ((a i).toReal : EReal) = a i :=
      fun i => EReal.coe_toReal (htop' i) (hbot i)
    have hsum1 : ∑ i, a i = ((∑ i, (a i).toReal : ℝ) : EReal) := by
      conv_lhs => arg 2; ext i; rw [← hcoe i]
      exact (ereal_coe_sum _ _).symm
    have hsum2 : ∑ i, (c : EReal) * a i = ((c * ∑ i, (a i).toReal : ℝ) : EReal) := by
      conv_lhs => arg 2; ext i; rw [← hcoe i, ← EReal.coe_mul]
      rw [← ereal_coe_sum, Finset.mul_sum]
    rw [hsum1, hsum2, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    exact mul_le_mul_iff_of_pos_left hc

open GenEmpLik.Expansion in
theorem solution (f : ℝ → EReal) (hA : AssumptionA f) {n : ℕ} (hn : 0 < n) {ρ ε C : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 ≤ C) (hCε : C * ε < 1)
    (hlow : ∀ t : ℝ, -1 ≤ t → ((2 * (1 - C * ε) * huber ε t : ℝ) : EReal) ≤ f (t + 1))
    (hup : ∀ t : ℝ, |t| ≤ ε → f (t + 1) ≤ (((1 + C * ε) * t ^ 2 : ℝ) : EReal))
    (z : Fin n → ℝ) :
    sSup ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Usm n ε C ρ) ≤
        robustMean f ρ z - empMean z ∧
      robustMean f ρ z - empMean z =
        sSup ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Umid f n ρ) ∧
      sSup ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Umid f n ρ) ≤
        sSup ((fun u : Fin n → ℝ => ∑ i, u i * z i) '' Ubig n ε C ρ) := by
  have _ := hC
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h1Cε : 0 < 1 - C * ε := by linarith
  let Φ : (Fin n → ℝ) → ℝ := fun u => ∑ i, u i * z i
  let Pset : Set (Fin n → ℝ) :=
    PhiDivRobust.Counterpart.probUncertaintySet f (fun _ => (1 : ℝ) / n) (ρ / n)
  have h0_usm : (0 : Fin n → ℝ) ∈ Usm n ε C ρ := by
    refine ⟨by simp, fun _ => by simp [le_of_lt hε], ?_⟩
    simp [le_of_lt hρ]
  have husm_sub_umid : Usm n ε C ρ ⊆ Umid f n ρ := by
    intro u ⟨hsum, hinf, hquad⟩
    refine ⟨hsum, ?_, ?_⟩
    · intro i
      have hi : -ε ≤ (n : ℝ) * u i := (abs_le.mp (hinf i)).1
      have h1 : -1 ≤ (n : ℝ) * u i := by linarith
      rw [div_le_iff₀ hn_pos]
      linarith
    · calc ∑ i, f ((n : ℝ) * u i + 1)
          ≤ ∑ i, (((1 + C * ε) * ((n : ℝ) * u i) ^ 2 : ℝ) : EReal) :=
            Finset.sum_le_sum fun i _ => hup _ (hinf i)
        _ = (((1 + C * ε) * ∑ i, ((n : ℝ) * u i) ^ 2 : ℝ) : EReal) := by
            rw [← ereal_coe_sum, Finset.mul_sum]
        _ ≤ (ρ : EReal) := EReal.coe_le_coe_iff.mpr hquad
  have humid_sub_ubig : Umid f n ρ ⊆ Ubig n ε C ρ := by
    intro u ⟨hsum, hge, hfsum⟩
    refine ⟨hsum, ?_⟩
    have hlow_sum : ((2 * (1 - C * ε) * ∑ i, huber ε ((n : ℝ) * u i) : ℝ) : EReal) ≤
        (ρ : EReal) := by
      calc ((2 * (1 - C * ε) * ∑ i, huber ε ((n : ℝ) * u i) : ℝ) : EReal)
          = ∑ i, ((2 * (1 - C * ε) * huber ε ((n : ℝ) * u i) : ℝ) : EReal) := by
            rw [Finset.mul_sum, ereal_coe_sum]
        _ ≤ ∑ i, f ((n : ℝ) * u i + 1) := by
            refine Finset.sum_le_sum fun i _ => hlow _ ?_
            have hi := (div_le_iff₀ hn_pos).mp (hge i)
            linarith
        _ ≤ (ρ : EReal) := hfsum
    have hreal : 2 * (1 - C * ε) * ∑ i, huber ε ((n : ℝ) * u i) ≤ ρ :=
      EReal.coe_le_coe_iff.mp hlow_sum
    exact (le_div_iff₀' (by positivity)).mpr hreal
  have hbdd_ubig : BddAbove (Φ '' Ubig n ε C ρ) := by
    let B : ℝ := ε + ρ / (2 * (1 - C * ε)) / ε
    refine ⟨B * ∑ i : Fin n, |z i|, ?_⟩
    rintro _ ⟨u, ⟨_, hhub⟩, rfl⟩
    have hnonneg : ∀ j : Fin n, 0 ≤ huber ε ((n : ℝ) * u j) := by
      intro j
      unfold huber
      split_ifs with hj
      · positivity
      · have hj' : ε < |(n : ℝ) * u j| := not_le.mp hj
        nlinarith
    have hub_le : ∀ i : Fin n, |u i| ≤ B := by
      intro i
      have hi_hub : huber ε ((n : ℝ) * u i) ≤ ρ / (2 * (1 - C * ε)) := by
        calc huber ε ((n : ℝ) * u i)
            ≤ ∑ j : Fin n, huber ε ((n : ℝ) * u j) :=
              Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
          _ ≤ ρ / (2 * (1 - C * ε)) := hhub
      have hnu_le : |(n : ℝ) * u i| ≤ B := by
        unfold huber at hi_hub
        split_ifs at hi_hub with hj
        · have : 0 ≤ ρ / (2 * (1 - C * ε)) / ε := by positivity
          linarith
        · have h1 : ε * |(n : ℝ) * u i| ≤ ρ / (2 * (1 - C * ε)) + ε ^ 2 / 2 := by linarith
          have h2 : |(n : ℝ) * u i| ≤ (ρ / (2 * (1 - C * ε)) + ε ^ 2 / 2) / ε :=
            (le_div_iff₀' hε).mpr h1
          have heq : (ρ / (2 * (1 - C * ε)) + ε ^ 2 / 2) / ε =
              ρ / (2 * (1 - C * ε)) / ε + ε / 2 := by field_simp
          rw [heq] at h2
          dsimp [B]
          linarith
      have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
      rw [abs_mul, abs_of_pos hn_pos] at hnu_le
      nlinarith [abs_nonneg (u i)]
    calc ∑ i, u i * z i
        ≤ ∑ i, |u i * z i| := Finset.sum_le_sum fun i _ => le_abs_self _
      _ = ∑ i, |u i| * |z i| := by simp_rw [abs_mul]
      _ ≤ ∑ i, B * |z i| :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hub_le i) (abs_nonneg _)
      _ = B * ∑ i, |z i| := by rw [← Finset.mul_sum]
  have hbdd_umid : BddAbove (Φ '' Umid f n ρ) :=
    hbdd_ubig.mono (Set.image_mono humid_sub_ubig)
  have hne_usm : (Φ '' Usm n ε C ρ).Nonempty := ⟨Φ 0, 0, h0_usm, rfl⟩
  have hne_umid : (Φ '' Umid f n ρ).Nonempty := hne_usm.mono (Set.image_mono husm_sub_umid)
  have humid_iff_pset : ∀ u : Fin n → ℝ,
      u ∈ Umid f n ρ ↔ (fun i => u i + (1 : ℝ) / n) ∈ Pset := by
    intro u
    simp only [Umid, Pset, PhiDivRobust.Counterpart.probUncertaintySet,
      PhiDivRobust.Counterpart.phiDiv, Set.mem_ofPred_eq, Pi.le_def, Pi.zero_apply]
    have hsum_iff : ∑ i : Fin n, u i = 0 ↔ ∑ i : Fin n, (u i + (1 : ℝ) / n) = 1 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have : (n : ℝ) * ((1 : ℝ) / n) = 1 := by field_simp
      rw [this]
      constructor <;> intro h <;> linarith
    have hge_iff : (∀ i : Fin n, -1 / (n : ℝ) ≤ u i) ↔ ∀ i : Fin n, 0 ≤ u i + (1 : ℝ) / n := by
      refine forall_congr' fun i => ?_
      have : -1 / (n : ℝ) = -((1 : ℝ) / n) := by ring
      rw [this]
      constructor <;> intro h <;> linarith
    have hdiv_eq : ∀ i : Fin n, (u i + (1 : ℝ) / n) / ((1 : ℝ) / n) = (n : ℝ) * u i + 1 := by
      intro i
      field_simp
    have hphi_iff : ∑ i : Fin n, (((1 : ℝ) / n : ℝ) : EReal) *
        f ((u i + (1 : ℝ) / n) / ((1 : ℝ) / n)) ≤ ((ρ / n : ℝ) : EReal) ↔
        ∑ i : Fin n, f ((n : ℝ) * u i + 1) ≤ (ρ : EReal) := by
      simp_rw [hdiv_eq]
      have hρ_eq : ρ / (n : ℝ) = ((1 : ℝ) / n) * ρ := by ring
      rw [hρ_eq]
      exact ereal_pos_mul_sum_le_iff (by positivity) _ (fun i => hA.1.ne_bot _)
    tauto
  have hmid_eq : robustMean f ρ z - empMean z = sSup (Φ '' Umid f n ρ) := by
    unfold robustMean
    change sSup ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' Pset) - empMean z = sSup (Φ '' Umid f n ρ)
    have hobj : ∀ u : Fin n → ℝ,
        ∑ i, (u i + (1 : ℝ) / n) * z i = Φ u + empMean z := by
      intro u
      dsimp [Φ, empMean]
      have : ∑ i, (u i + (1 : ℝ) / n) * z i = ∑ i, u i * z i + ∑ i, ((1 : ℝ) / n) * z i := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [this, ← Finset.mul_sum, one_div]
    have hbdd_pset : BddAbove ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' Pset) := by
      rcases hbdd_umid with ⟨M, hM⟩
      refine ⟨M + empMean z, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      let u : Fin n → ℝ := fun i => p i - (1 : ℝ) / n
      have hpu : (fun i => u i + (1 : ℝ) / n) = p := by ext i; dsimp [u]; ring
      have hu : u ∈ Umid f n ρ := (humid_iff_pset u).mpr (hpu ▸ hp)
      have h1 : Φ u ≤ M := hM ⟨u, hu, rfl⟩
      have h2 : ∑ i, p i * z i = Φ u + empMean z := by
        have hp_eq : ∀ i, p i = u i + (1 : ℝ) / n := fun i => by dsimp [u]; ring
        simp_rw [hp_eq]
        exact hobj u
      dsimp only
      linarith
    have hne_pset : ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' Pset).Nonempty := by
      rcases hne_umid with ⟨_, u, hu, rfl⟩
      exact ⟨_, _, (humid_iff_pset u).mp hu, rfl⟩
    apply le_antisymm
    · rw [sub_le_iff_le_add]
      refine csSup_le hne_pset ?_
      rintro _ ⟨p, hp, rfl⟩
      let u : Fin n → ℝ := fun i => p i - (1 : ℝ) / n
      have hpu : (fun i => u i + (1 : ℝ) / n) = p := by ext i; dsimp [u]; ring
      have hu : u ∈ Umid f n ρ := (humid_iff_pset u).mpr (hpu ▸ hp)
      have h1 : Φ u ≤ sSup (Φ '' Umid f n ρ) := le_csSup hbdd_umid ⟨u, hu, rfl⟩
      have h2 : ∑ i, p i * z i = Φ u + empMean z := by
        have hp_eq : ∀ i, p i = u i + (1 : ℝ) / n := fun i => by dsimp [u]; ring
        simp_rw [hp_eq]
        exact hobj u
      dsimp only
      linarith
    · refine csSup_le hne_umid ?_
      rintro _ ⟨u, hu, rfl⟩
      have hp : (fun i => u i + (1 : ℝ) / n) ∈ Pset := (humid_iff_pset u).mp hu
      have h1 : ∑ i, (u i + (1 : ℝ) / n) * z i ≤
          sSup ((fun p : Fin n → ℝ => ∑ i, p i * z i) '' Pset) :=
        le_csSup hbdd_pset ⟨_, hp, rfl⟩
      linarith [hobj u]
  refine ⟨?_, hmid_eq, ?_⟩
  · rw [hmid_eq]
    exact csSup_le_csSup hbdd_umid hne_usm (Set.image_mono husm_sub_umid)
  · exact csSup_le_csSup hbdd_ubig hne_umid (Set.image_mono humid_sub_ubig)
