-- Prove2me | solution 1 for BirthdayEntropy.Soundness.flattening_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:04:41.478795+00:00
-- url     : https://prove2.me/submissions/f4f222c9-1979-48e4-83eb-3bc07c7ffa53

import Theorems.Thm_BirthdayEntropy_Soundness_cross_consistent_entropy_bound
import Definitions.Def_BirthdayEntropy_Soundness_Counting
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Theorems.Thm_OAI_ThorpCompatibility_Law_condEntropy_eq_mean
import Theorems.Thm_OAI_ThorpCompatibility_Law_condEntropy_le_prediction
import Theorems.Thm_OAI_ThorpCompatibility_Law_gibbs_le

noncomputable section
open scoped Classical
open Finset OAI.ThorpCompatibility
namespace BirthdayEntropy.Soundness.Info
variable {α β γ δ η : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [Fintype η]

lemma mean_map (P : Law α) (f : α → β) (g : β → ℝ) :
    (P.map f).mean g = P.mean (fun a => g (f a)) := by
  classical
  simp only [Law.mean, Law.map, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

lemma mean_congr_support (P : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < P.mass a → f a = g a) : P.mean f = P.mean g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P.mass a = 0
  · simp [ha]
  · rw [h a (lt_of_le_of_ne (P.nonneg a) (Ne.symm ha))]

lemma mass_le_map (P : Law α) (f : α → β) (a : α) : P.mass a ≤ (P.map f).mass (f a) := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b => if f b = f a then P.mass b else 0)
    (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
  simpa [Law.map] using h

lemma map_mass_pos (P : Law α) (f : α → β) {a : α} (ha : 0 < P.mass a) :
    0 < (P.map f).mass (f a) := lt_of_lt_of_le ha (mass_le_map P f a)

lemma entropy_fibers (P : Law α) (X : α → β) (Y : α → γ)
    (h : ∀ a b, X a = X b ↔ Y a = Y b) : (P.map X).entropy = (P.map Y).entropy := by
  rw [Law.entropy, Law.entropy, mean_map, mean_map]
  congr 1
  apply congrArg
  funext a
  congr 1
  simp only [Law.map]
  apply Finset.sum_congr rfl
  intro b _
  rw [h b a]

lemma mean_sub (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a - g a) = P.mean f - P.mean g := by
  simp [Law.mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_mono (P : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < P.mass a → f a ≤ g a) : P.mean f ≤ P.mean g := by
  apply Finset.sum_le_sum
  intro a ha
  by_cases hp : 0 < P.mass a
  · exact mul_le_mul_of_nonneg_left (h a hp) (P.nonneg a)
  · have hz : P.mass a = 0 := le_antisymm (le_of_not_gt hp) (P.nonneg a)
    simp [hz]

lemma mean_const (P : Law α) (c : ℝ) : P.mean (fun _ => c) = c := by
  simp [Law.mean,← Finset.sum_mul,P.total]

lemma mean_add (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a + g a) = P.mean f + P.mean g := by
  simp [Law.mean,mul_add,Finset.sum_add_distrib]

lemma mean_mul (P : Law α) (c : ℝ) (f : α → ℝ) :
    P.mean (fun a => c * f a) = c * P.mean f := by
  simp only [Law.mean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma predict_mass (P : Law α) (X : α → β) (Y : α → γ) {a : α} (ha : 0 < P.mass a) :
    (P.predict X Y (Y a)).mass (X a) = P.condMass X Y a := by
  have hp : 0 < P.prob (fun b => Y b = Y a) := by
    change 0 < ∑ b, if Y b = Y a then P.mass b else 0
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun b => if Y b = Y a then P.mass b else 0)
      (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
    simp only [ite_true] at h
    exact ha.trans_le h
  have heq : P.prob (fun b => Y b = Y a) = (P.map Y).mass (Y a) := by
    simp [Law.prob, Law.map, mul_ite]
  unfold Law.predict Law.restrict
  rw [dif_pos hp]
  dsimp [Law.map, Law.condMass]
  simp only [Law.map] at heq
  rw [← heq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp_all

lemma condEntropy_condition (P : Law α) (X : α → β) (Y : α → γ) (Z : α → δ) :
    P.condEntropy X (fun a => (Y a,Z a)) ≤ P.condEntropy X Y := by
  have hs : ∀ a, 0 < P.mass a → 0 < (P.predict X Y (Y a)).mass (X a) := by
    intro a ha
    rw [predict_mass P X Y ha]
    exact div_pos (map_mass_pos P _ ha) (map_mass_pos P _ ha)
  have h := P.condEntropy_le_prediction X (fun a => (Y a,Z a))
    (fun yz => P.predict X Y yz.1) hs
  rw [P.condEntropy_eq_mean X Y]
  apply le_trans h
  apply le_of_eq
  congr 1
  apply mean_congr_support
  intro a ha
  rw [predict_mass P X Y ha]

lemma mutualInfo_nonneg (P : Law α) (X : α → β) (Y : α → γ) :
    0 ≤ mutualInfo P X Y := by
  have hs : ∀ a, 0 < P.mass a → 0 < (P.map X).mass (X a) := fun a ha => map_mass_pos P X ha
  have h := P.condEntropy_le_prediction X Y (fun _ => P.map X) hs
  rw [← mean_map P X (fun x => Real.log ((P.map X).mass x))] at h
  change (P.map (fun a => (X a,Y a))).entropy - (P.map Y).entropy ≤ (P.map X).entropy at h
  unfold mutualInfo
  linarith

lemma mutualInfo_left (P : Law α) (X : α → β) (Y : α → γ) (f : β → δ) :
    mutualInfo P (fun a => f (X a)) Y ≤ mutualInfo P X Y := by
  have h := condEntropy_condition P X (fun a => f (X a)) Y
  unfold Law.condEntropy at h
  have h1 : (P.map (fun a => (X a, f (X a)))).entropy = (P.map X).entropy := by
    apply entropy_fibers
    intro a b
    simp only [Prod.mk.injEq]
    exact ⟨And.left, fun h => ⟨h, congrArg f h⟩⟩
  have h2 : (P.map (fun a => (X a, (f (X a),Y a)))).entropy = (P.map (fun a => (X a,Y a))).entropy := by
    apply entropy_fibers
    intro a b
    simp only [Prod.mk.injEq]
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · exact fun h => ⟨h.1,congrArg f h.1,h.2⟩
  rw [h1,h2] at h
  unfold mutualInfo
  linarith

lemma mutualInfo_symm (P : Law α) (X : α → β) (Y : α → γ) :
    mutualInfo P X Y = mutualInfo P Y X := by
  have h : (P.map (fun a => (X a,Y a))).entropy = (P.map (fun a => (Y a,X a))).entropy := by
    apply entropy_fibers
    intro a b
    simp [and_comm]
  unfold mutualInfo
  rw [h]
  ring

lemma mutualInfo_process (P : Law α) (X : α → β) (Y : α → γ) (f : β → δ) (g : γ → η) :
    mutualInfo P (fun a => f (X a)) (fun a => g (Y a)) ≤ mutualInfo P X Y := by
  calc
    _ ≤ mutualInfo P X (fun a => g (Y a)) := mutualInfo_left P X _ f
    _ = mutualInfo P (fun a => g (Y a)) X := mutualInfo_symm _ _ _
    _ ≤ mutualInfo P Y X := mutualInfo_left P Y X g
    _ = mutualInfo P X Y := mutualInfo_symm _ _ _
end BirthdayEntropy.Soundness.Info

noncomputable section
open scoped Classical
open Finset OAI.ThorpCompatibility BirthdayEntropy.Soundness

private lemma mean_map {α τ : Type*} [Fintype α] [Fintype τ]
    (Q : Law α) (F : α → τ) (g : τ → ℝ) :
    (Q.map F).mean g = Q.mean (fun a => g (F a)) := by
  classical
  unfold Law.mean Law.map
  simp only
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  ext a
  simp

private lemma uniform_mass {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty)
    (a : α) : (uniformOn Ω hΩ).mass a = if a ∈ Ω then 1 / (Ω.card : ℝ) else 0 := by
  classical
  unfold uniformOn Law.map Law.uniform
  simp only
  change (∑ x : Ω, if x.val = a then 1 / (Fintype.card Ω : ℝ) else 0) = _
  rw [Finset.sum_coe_sort Ω (fun x : α => if x = a then 1 / (Fintype.card Ω : ℝ) else 0)]
  simp

private lemma uniform_mean {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty)
    (g : α → ℝ) : (uniformOn Ω hΩ).mean g = (∑ a ∈ Ω, g a) / Ω.card := by
  classical
  unfold Law.mean
  simp_rw [uniform_mass, ite_mul, zero_mul]
  simp [Finset.sum_filter, Finset.sum_mul, div_eq_mul_inv, mul_comm]

private lemma uniform_map_mass {α τ : Type*} [Fintype α] [Fintype τ]
    (Ω : Finset α) (hΩ : Ω.Nonempty) (F : α → τ) (f : τ) :
    ((uniformOn Ω hΩ).map F).mass f = ((cell Ω F f).card : ℝ) / Ω.card := by
  classical
  unfold Law.map
  simp only
  simp_rw [uniform_mass]
  have hf : Finset.univ.filter (fun x => F x = f) ∩ Ω = cell Ω F f := by
    ext a
    simp [cell, and_comm]
  simp [Finset.sum_ite, hf, div_eq_mul_inv]

private lemma uniform_mean_le {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty)
    (f g : α → ℝ) (h : ∀ a ∈ Ω, f a ≤ g a) :
    (uniformOn Ω hΩ).mean f ≤ (uniformOn Ω hΩ).mean g := by
  rw [uniform_mean, uniform_mean]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (by positivity)

private lemma uniform_mean_const {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty)
    (c : ℝ) : (uniformOn Ω hΩ).mean (fun _ => c) = c := by
  rw [uniform_mean]
  simp [hΩ.card_pos.ne', mul_div_cancel_left₀]

private lemma uniform_mean_sub {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty)
    (f g : α → ℝ) : (uniformOn Ω hΩ).mean (fun a => f a - g a) =
      (uniformOn Ω hΩ).mean f - (uniformOn Ω hΩ).mean g := by
  simp [uniform_mean, Finset.sum_sub_distrib, sub_div]

private lemma cell_nonempty {α τ : Type*} [Fintype α] [Fintype τ]
    (Ω : Finset α) (F : α → τ) {a : α} (ha : a ∈ Ω) : (cell Ω F (F a)).Nonempty := by
  exact ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩

private lemma entropy_identity {α τ : Type*} [Fintype α] [Fintype τ]
    (Ω : Finset α) (hΩ : Ω.Nonempty) (F : α → τ) :
    ((uniformOn Ω hΩ).map F).entropy = Real.log (Ω.card : ℝ) -
      (uniformOn Ω hΩ).mean (fun a => Real.log ((cell Ω F (F a)).card : ℝ)) := by
  rw [Law.entropy, mean_map]
  have heq : (uniformOn Ω hΩ).mean (fun a => Real.log (((uniformOn Ω hΩ).map F).mass (F a))) =
      (uniformOn Ω hΩ).mean (fun a => Real.log ((cell Ω F (F a)).card : ℝ) - Real.log (Ω.card : ℝ)) := by
    rw [uniform_mean, uniform_mean]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    rw [uniform_map_mass, Real.log_div]
    · exact_mod_cast (cell_nonempty Ω F ha).card_pos.ne'
    · exact_mod_cast hΩ.card_pos.ne'
  rw [heq, uniform_mean_sub, uniform_mean_const]
  ring

private lemma uniform_entropy {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty) :
    (uniformOn Ω hΩ).entropy = Real.log (Ω.card : ℝ) := by
  rw [Law.entropy, uniform_mean]
  have heq : ∑ a ∈ Ω, Real.log ((uniformOn Ω hΩ).mass a) =
      (Ω.card : ℝ) * Real.log (1 / (Ω.card : ℝ)) := by
    calc
      _ = ∑ a ∈ Ω, Real.log (1 / (Ω.card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [uniform_mass, if_pos ha]
      _ = _ := by simp
  rw [heq]
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast hΩ.card_pos.ne')]
  simp


private lemma cross_flatten {n m ℓ r : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ))
    (X : Tuple n ℓ r) (hX : X ∈ accepted φ H r) : CrossConsistent (flatten X) := by
  classical
  intro i b hi hj
  obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hj
  have hadj := (Finset.mem_filter.mp hX).2.2.2 a c
  have hcons := hadj.2.1 i
  have ha' : (i,b) ∈ signed (X.1 a) ∪ signed (X.2 c) := Finset.mem_union_left _ ha
  have hc' : (i,!b) ∈ signed (X.1 a) ∪ signed (X.2 c) := Finset.mem_union_right _ hc
  cases b <;> exact hcons (by simpa [and_comm] using And.intro ha' hc')


private lemma entropy_supported {α τ : Type*} [Fintype α] [Fintype τ]
    (Ω : Finset α) (hΩ : Ω.Nonempty) (F : α → τ) (S : Finset τ)
    (hS : ∀ a ∈ Ω, F a ∈ S) :
    ((uniformOn Ω hΩ).map F).entropy ≤ Real.log (S.card : ℝ) := by
  have hSp : 0 < (S.card : ℝ) := by
    obtain ⟨a,ha⟩ := hΩ
    exact_mod_cast Finset.card_pos.mpr ⟨F a,hS a ha⟩
  have hz : 0 < ∑ s, if s ∈ S then (1 : ℝ) else 0 := by simpa using hSp
  have hs : ∀ s, (if s ∈ S then (1 : ℝ) else 0) = 0 →
      ((uniformOn Ω hΩ).map F).mass s = 0 := by
    intro s hzero
    have hnot : s ∉ S := by simpa using hzero
    change (∑ a, if F a = s then (uniformOn Ω hΩ).mass a else 0) = 0
    apply Finset.sum_eq_zero
    intro a ha
    by_cases heq : F a = s
    · rw [if_pos heq, uniform_mass]
      rw [if_neg (by intro ha; exact hnot (heq ▸ hS a ha))]
    · rw [if_neg heq]
  have h := ((uniformOn Ω hΩ).map F).gibbs_le (fun s => if s ∈ S then 1 else 0)
    (by intro s; split_ifs <;> norm_num) hz hs
  have hzlog : (fun s : τ => Real.log (if s ∈ S then (1:ℝ) else 0)) = (fun _ => 0) := by
    funext s
    split_ifs <;> simp
  rw [hzlog] at h
  simpa [Law.entropy,Law.mean] using h

private lemma mi_accepted {n m ℓ r : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ))
    (hH : H.card = Nat.choose n ℓ) (hΩ : (accepted φ H r).Nonempty) :
    mutualInfo (uniformOn (accepted φ H r) hΩ) Prod.fst Prod.snd ≤
      Real.log (1 / acceptanceProbability φ H r) := by
  classical
  let Ω := accepted φ H r
  let Q := uniformOn Ω hΩ
  let S : Finset (Fin r → Vertex n ℓ) := Fintype.piFinset (fun _ => H)
  have hL := entropy_supported Ω hΩ Prod.fst S (by
    intro X hX
    simpa [S] using (Finset.mem_filter.mp hX).2.1)
  have hR := entropy_supported Ω hΩ Prod.snd S (by
    intro X hX
    simpa [S] using (Finset.mem_filter.mp hX).2.2.1)
  have hmap : Q.map (fun a => (a.1,a.2)) = Q := by
    apply Law.ext
    intro a
    simp only [Law.map,Prod.eta]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hba
      simp [hba]
    · intro hnot
      exact (hnot (Finset.mem_univ a)).elim
  have hMpos : (0 : ℝ) < (H.card : ℝ)^(2*r) := by
    have hSp : 0 < S.card := Finset.card_pos.mpr ⟨hΩ.choose.1, by simpa [S] using (Finset.mem_filter.mp hΩ.choose_spec).2.1⟩
    have hSc : (S.card : ℝ) = (H.card : ℝ)^r := by simp [S]
    have hSp' : (0 : ℝ) < S.card := by exact_mod_cast hSp
    rw [hSc] at hSp'
    rw [mul_comm 2 r,pow_mul]
    positivity
  have hΩpos : (0 : ℝ) < Ω.card := by exact_mod_cast hΩ.card_pos
  have hSlog : Real.log (S.card : ℝ) = (r : ℝ) * Real.log (H.card : ℝ) := by simp [S,Real.log_pow]
  have hlog : Real.log (1 / acceptanceProbability φ H r) =
      2*(r : ℝ)*Real.log (H.card : ℝ) - Real.log (Ω.card : ℝ) := by
    change Real.log (1 / ((Ω.card : ℝ) / (H.card : ℝ)^(2*r))) = _
    rw [one_div_div,Real.log_div hMpos.ne' hΩpos.ne',Real.log_pow,Nat.cast_mul,Nat.cast_ofNat]
  unfold mutualInfo
  change (Q.map Prod.fst).entropy + (Q.map Prod.snd).entropy -
    (Q.map (fun a => (a.1,a.2))).entropy ≤ _
  rw [hmap,show Q.entropy = Real.log (Ω.card : ℝ) from uniform_entropy Ω hΩ,hlog]
  rw [hSlog] at hL hR
  linarith

theorem solution (d ε : ℝ) (hd : 1 ≤ d) (hε : 0 < ε) :
    ∃ C D₁ D₂ : ℝ, 0 < C ∧ 0 ≤ D₁ ∧ 0 ≤ D₂ ∧
      ∀ (n m : ℕ) (φ : CSP n m), Source φ d → Gap φ ε →
      ∀ (ℓ : ℕ), 2 ≤ ℓ → (ℓ : ℝ) < min (beta d ε) (1/2) * n →
      ∀ (H : Finset (Vertex n ℓ)), H.card = Nat.choose n ℓ →
      ∀ (r : ℕ) (hΩ : (accepted φ H r).Nonempty),
        let Q := uniformOn (accepted φ H r) hΩ
        let E := Q.mean (fun X => energy ℓ (beta d ε) (flatten X))
        (Q.map flatten).entropy ≤
          5 * mutualInfo Q Prod.fst Prod.snd + C * logScale n ℓ * E +
            D₁ * Real.log ((n : ℝ) + 1) ∧
        (Q.map flatten).entropy ≤
          5 * Real.log (1 / acceptanceProbability φ H r) + C * logScale n ℓ * E +
            D₂ * Real.log (n : ℝ) := by
  classical
  have hβ : 0 < beta d ε := by
    unfold beta
    exact lt_min (by norm_num) (div_pos hε (by linarith))
  have hβ1 : beta d ε ≤ 1 := (min_le_left _ _).trans (by norm_num)
  refine ⟨16+2/beta d ε,0,0,by positivity,le_rfl,le_rfl,?_⟩
  intro n m φ hsrc hgap ℓ hℓ hscale H hH r hΩ
  dsimp only
  let Q := uniformOn (accepted φ H r) hΩ
  have hn : 0 < (n : ℝ) := by
    by_contra h
    have hle : min (beta d ε) (1/2) * (n : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (lt_min hβ (by norm_num))) (le_of_not_gt h)
    have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hx : 0 < ratio n ℓ := div_pos (by exact_mod_cast lt_of_lt_of_le (by decide : 0<2) hℓ) hn
  have hxhalf : ratio n ℓ ≤ 1/2 := by
    apply (div_le_iff₀ hn).mpr
    have hmin := min_le_right (beta d ε) (1/2)
    nlinarith
  have hcross : ∀ X, 0 < Q.mass X → CrossConsistent (flatten X) := by
    intro X hX
    have hmem : X ∈ accepted φ H r := by
      by_contra hnot
      have hz : Q.mass X = 0 := by rw [uniform_mass,if_neg hnot]
      linarith
    exact cross_flatten φ H X hmem
  have h := BirthdayEntropy.Soundness.cross_consistent_entropy_bound Q Prod.fst Prod.snd
    (fun L => Finset.univ.biUnion (fun i => signed (L i)))
    (fun R => Finset.univ.biUnion (fun j => signed (R j)))
    (beta d ε) hβ hβ1 hx hxhalf hcross
  change (Q.map flatten).entropy ≤ mutualInfo Q Prod.fst Prod.snd +
    (16+2/beta d ε)*logScale n ℓ*Q.mean (fun X => energy ℓ (beta d ε) (flatten X)) at h
  have hI := Info.mutualInfo_nonneg Q Prod.fst Prod.snd
  have hIp := mi_accepted φ H hH hΩ
  change mutualInfo Q Prod.fst Prod.snd ≤ _ at hIp
  constructor <;> simp only [zero_mul,add_zero] <;> linarith
