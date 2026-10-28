-- Prove2me | solution 1 for FranklKupavskii2022.EMC.indicator_covariance_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:49:32.601991+00:00
-- url     : https://prove2.me/submissions/3f39f4c3-2e90-4688-886f-d7adb6c1e903

import Definitions.Def_FranklKupavskii2022_EMC_tMatchings
import Init
import Mathlib


namespace FranklKupavskii2022.EMC.Exchange
open Finset
set_option maxHeartbeats 1000000

theorem mem_matching {m l t : ℕ} (B : Fin t → Finset ℕ) :
    B ∈ tMatchings m l t ↔
      (∀ i, B i ⊆ Icc 1 m ∧ (B i).card = l) ∧
      ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
  simp [tMatchings,mem_powersetCard]

def blocks (l t : ℕ) (i : Fin t) : Finset ℕ := Icc (i.val*l+1) ((i.val+1)*l)

theorem blocks_mem (m l t : ℕ) (hm : t*l ≤ m) : blocks l t ∈ tMatchings m l t := by
  rw [mem_matching]
  constructor
  · intro i
    constructor
    · intro x hx
      simp only [blocks,mem_Icc] at hx ⊢
      have hi : (i.val+1)*l ≤ t*l := Nat.mul_le_mul_right l (by omega)
      omega
    · simp only [blocks,Nat.card_Icc,Nat.add_mul,one_mul]
      omega
  · intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    simp only [blocks,mem_Icc] at hxi hxj
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h|h
    · have hi : (i.val+1)*l ≤ j.val*l := Nat.mul_le_mul_right l h
      omega
    · have hj : (j.val+1)*l ≤ i.val*l := Nat.mul_le_mul_right l h
      omega

theorem matching_nonempty (m l t : ℕ) (hm : t*l ≤ m) : (tMatchings m l t).Nonempty :=
  ⟨blocks l t,blocks_mem m l t hm⟩

theorem reindex_mem {m l t : ℕ} (e : Equiv.Perm (Fin t))
    {B : Fin t → Finset ℕ} (hB : B ∈ tMatchings m l t) :
    (fun i => B (e i)) ∈ tMatchings m l t := by
  rw [mem_matching] at hB ⊢
  exact ⟨fun i => hB.1 (e i),fun i j hij => hB.2 (e i) (e j) (fun h => hij (e.injective h))⟩

theorem sum_reindex (m l t : ℕ) (e : Equiv.Perm (Fin t))
    (X : (Fin t → Finset ℕ) → ℝ) :
    (∑ B ∈ tMatchings m l t, X (fun i => B (e i))) = ∑ B ∈ tMatchings m l t, X B := by
  apply sum_bij (fun B _ i => B (e i))
  · intro B hB
    exact reindex_mem e hB
  · intro B hB C hC h
    funext i
    have h' := congrFun h (e.symm i)
    simpa using h'
  · intro B hB
    refine ⟨fun i => B (e.symm i),reindex_mem e.symm hB,?_⟩
    funext i
    simp
  · intros
    rfl

theorem avg_reindex (m l t : ℕ) (e : Equiv.Perm (Fin t))
    (X : (Fin t → Finset ℕ) → ℝ) :
    avg m l t (fun B => X (fun i => B (e i))) = avg m l t X := by
  simp only [avg,sum_reindex]

theorem avg_indicator_eq (m l t : ℕ) (G : Finset (Finset ℕ)) (i j : Fin t) :
    avg m l t (etaI G i) = avg m l t (etaI G j) := by
  change avg m l t (fun B => if B i ∈ G then (1:ℝ) else 0) =
    avg m l t (fun B => if B j ∈ G then (1:ℝ) else 0)
  have h := avg_reindex m l t (Equiv.swap i j) (fun B => if B i ∈ G then (1:ℝ) else 0)
  simpa only [Equiv.swap_apply_left] using h.symm

end FranklKupavskii2022.EMC.Exchange

namespace FranklKupavskii2022.EMC.Exchange
open Finset
set_option maxHeartbeats 1000000

theorem avg_add (m l t : ℕ) (X Y : (Fin t → Finset ℕ) → ℝ) :
    avg m l t (fun B => X B+Y B) = avg m l t X+avg m l t Y := by
  simp only [avg,sum_add_distrib,add_div]

theorem avg_sub (m l t : ℕ) (X Y : (Fin t → Finset ℕ) → ℝ) :
    avg m l t (fun B => X B-Y B) = avg m l t X-avg m l t Y := by
  simp only [avg,sum_sub_distrib,sub_div]

theorem avg_smul (m l t : ℕ) (c : ℝ) (X : (Fin t → Finset ℕ) → ℝ) :
    avg m l t (fun B => c*X B) = c*avg m l t X := by
  simp only [avg,← mul_sum,mul_div_assoc]

theorem avg_const (m l t : ℕ) (hm : t*l ≤ m) (c : ℝ) :
    avg m l t (fun _ => c) = c := by
  have hn : (tMatchings m l t).card ≠ 0 := ne_of_gt (card_pos.mpr (matching_nonempty m l t hm))
  simp [avg,hn]

theorem avg_nonneg (m l t : ℕ) (X : (Fin t → Finset ℕ) → ℝ)
    (hX : ∀ B ∈ tMatchings m l t, 0 ≤ X B) : 0 ≤ avg m l t X := by
  exact div_nonneg (sum_nonneg hX) (Nat.cast_nonneg _)

theorem avg_mono (m l t : ℕ) (X Y : (Fin t → Finset ℕ) → ℝ)
    (h : ∀ B ∈ tMatchings m l t, X B ≤ Y B) : avg m l t X ≤ avg m l t Y := by
  exact div_le_div_of_nonneg_right (sum_le_sum h) (Nat.cast_nonneg _)

theorem avg_sum {ι : Type*} [Fintype ι] (m l t : ℕ)
    (X : ι → (Fin t → Finset ℕ) → ℝ) :
    avg m l t (fun B => ∑ i, X i B) = ∑ i, avg m l t (X i) := by
  unfold avg
  rw [sum_comm,sum_div]

theorem centered_square (m l t : ℕ) (hm : t*l ≤ m) (X : (Fin t → Finset ℕ) → ℝ) :
    avg m l t (fun B => (X B-avg m l t X)^2) = cov m l t X X := by
  have he (B) : (X B-avg m l t X)^2 = X B*X B - (2*avg m l t X)*X B + (avg m l t X)^2 := by ring
  simp_rw [he]
  rw [avg_add,avg_sub,avg_smul,avg_const m l t hm]
  unfold cov
  ring

theorem cov_self_nonneg (m l t : ℕ) (hm : t*l ≤ m) (X : (Fin t → Finset ℕ) → ℝ) :
    0 ≤ cov m l t X X := by
  rw [← centered_square m l t hm]
  exact avg_nonneg m l t _ (fun B _ => sq_nonneg _)

theorem cov_comm (m l t : ℕ) (X Y : (Fin t → Finset ℕ) → ℝ) :
    cov m l t X Y = cov m l t Y X := by
  simp only [cov,mul_comm]

theorem cov_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (m l t : ℕ)
    (X : ι → (Fin t → Finset ℕ) → ℝ) (Y : κ → (Fin t → Finset ℕ) → ℝ) :
    cov m l t (fun B => ∑ i, X i B) (fun B => ∑ j, Y j B) =
      ∑ i, ∑ j, cov m l t (X i) (Y j) := by
  simp only [cov,sum_mul,mul_sum,avg_sum,sum_sub_distrib]
  congr 1 <;> exact sum_comm

theorem indicator_variance (m l t : ℕ) (G : Finset (Finset ℕ)) (i : Fin t) :
    cov m l t (etaI G i) (etaI G i) =
      avg m l t (etaI G i)*(1-avg m l t (etaI G i)) := by
  have he (B) : etaI G i B*etaI G i B = etaI G i B := by
    unfold etaI; split_ifs <;> norm_num
  simp only [cov,he]
  ring

theorem indicator_bounds (m l t : ℕ) (hm : t*l ≤ m) (G : Finset (Finset ℕ)) (i : Fin t) :
    0 ≤ avg m l t (etaI G i) ∧ avg m l t (etaI G i) ≤ 1 := by
  constructor
  · exact avg_nonneg m l t _ (by intros; unfold etaI; split_ifs <;> norm_num)
  · rw [← avg_const m l t hm 1]
    exact avg_mono m l t _ _ (by intros; unfold etaI; split_ifs <;> norm_num)

theorem eta_sum {t : ℕ} (G : Finset (Finset ℕ)) (B : Fin t → Finset ℕ) :
    (eta G B : ℝ) = ∑ i, etaI G i B := by
  classical
  unfold eta etaI
  rw [card_filter]
  simp only [Nat.cast_sum]
  apply sum_congr rfl
  intro i _
  split_ifs <;> norm_num

theorem avg_eta (m l t : ℕ) (G : Finset (Finset ℕ)) (i : Fin t) :
    avg m l t (fun B => (eta G B : ℝ)) = (t:ℝ)*avg m l t (etaI G i) := by
  simp_rw [eta_sum,avg_sum]
  calc
    _ = ∑ _j : Fin t, avg m l t (etaI G i) :=
      sum_congr rfl (fun j _ => avg_indicator_eq m l t G j i)
    _ = _ := by simp

end FranklKupavskii2022.EMC.Exchange

namespace FranklKupavskii2022.EMC.Exchange
open Finset
set_option maxHeartbeats 1000000

theorem pair_permutation {α : Type*} [DecidableEq α] (i j k r : α)
    (hij : i ≠ j) (hkr : k ≠ r) : ∃ e : Equiv.Perm α, e i = k ∧ e j = r := by
  let s := Equiv.swap i k
  have hsi : s i = k := Equiv.swap_apply_left i k
  have hsj : s j ≠ k := by
    intro h
    have : s j = s i := h.trans hsi.symm
    exact hij (s.injective this).symm
  refine ⟨s.trans (Equiv.swap (s j) r),?_,?_⟩
  · change Equiv.swap (s j) r (s i) = k
    rw [hsi]
    exact Equiv.swap_apply_of_ne_of_ne hsj.symm hkr
  · exact Equiv.swap_apply_left (s j) r

theorem cov_indicator_eq (m l t : ℕ) (G : Finset (Finset ℕ))
    (i j k r : Fin t) (hij : i ≠ j) (hkr : k ≠ r) :
    cov m l t (etaI G i) (etaI G j) = cov m l t (etaI G k) (etaI G r) := by
  obtain ⟨e,hi,hj⟩ := pair_permutation i j k r hij hkr
  have h := avg_reindex m l t e (fun B => etaI G i B*etaI G j B)
  have he : (fun B => etaI G i (fun a => B (e a))*etaI G j (fun a => B (e a))) =
      (fun B => etaI G k B*etaI G r B) := by
    funext B
    dsimp only [etaI]
    simp only [hi,hj]
  rw [he] at h
  unfold cov
  rw [h,avg_indicator_eq m l t G k i,avg_indicator_eq m l t G r j]

theorem variance_eta (m l t : ℕ) (G : Finset (Finset ℕ))
    (i j : Fin t) (hij : i ≠ j) :
    cov m l t (fun B => (eta G B : ℝ)) (fun B => (eta G B : ℝ)) =
      (t:ℝ)*(avg m l t (etaI G i)*(1-avg m l t (etaI G i))) +
      (t:ℝ)*((t:ℝ)-1)*cov m l t (etaI G i) (etaI G j) := by
  classical
  simp_rw [eta_sum]
  rw [cov_sum]
  have hc (a b : Fin t) : cov m l t (etaI G a) (etaI G b) =
      if a=b then avg m l t (etaI G i)*(1-avg m l t (etaI G i))
      else cov m l t (etaI G i) (etaI G j) := by
    by_cases hab : a=b
    · subst b
      simp only [ite_true,indicator_variance,avg_indicator_eq m l t G a i]
    · rw [if_neg hab]
      exact cov_indicator_eq m l t G a b i j hab hij
  have hreplace : (∑ a : Fin t, ∑ b : Fin t, cov m l t (etaI G a) (etaI G b)) =
      ∑ a : Fin t, ∑ b : Fin t, if a=b then avg m l t (etaI G i)*(1-avg m l t (etaI G i))
        else cov m l t (etaI G i) (etaI G j) := by
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    exact hc a b
  rw [hreplace]
  have hs (a : Fin t) :
      (∑ b : Fin t, if a=b then avg m l t (etaI G i)*(1-avg m l t (etaI G i))
        else cov m l t (etaI G i) (etaI G j)) =
      avg m l t (etaI G i)*(1-avg m l t (etaI G i)) +
        ((t:ℝ)-1)*cov m l t (etaI G i) (etaI G j) := by
    rw [← add_sum_erase univ _ (mem_univ a)]
    simp only [ite_true]
    have he (b : Fin t) (hb : b ∈ univ.erase a) : a ≠ b := (mem_erase.mp hb).1.symm
    simp only [sum_congr rfl (fun b hb => if_neg (he b hb))]
    simp only [sum_const,nsmul_eq_mul,card_erase_of_mem (mem_univ a),card_univ,Fintype.card_fin]
    rw [Nat.cast_sub (by omega : 1 ≤ t)]
    norm_num
  simp_rw [hs]
  simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]
  ring

theorem covariance_lower_bound (m l t : ℕ) (hm : t*l ≤ m) (G : Finset (Finset ℕ))
    (i j : Fin t) (hij : i ≠ j) :
    -(avg m l t (etaI G i)*(1-avg m l t (etaI G i)))/((t:ℝ)-1) ≤
      cov m l t (etaI G i) (etaI G j) := by
  have ht : 2 ≤ t := by
    have hi := i.isLt
    have hj := j.isLt
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    omega
  have hpos : 0 < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hden : 0 < (t:ℝ)-1 := by
    have htR : (2:ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hv := cov_self_nonneg m l t hm (fun B => (eta G B : ℝ))
  rw [variance_eta m l t G i j hij] at hv
  apply (div_le_iff₀ hden).mpr
  nlinarith

end FranklKupavskii2022.EMC.Exchange

namespace FranklKupavskii2022.EMC.Exchange
open Finset
set_option maxHeartbeats 1000000

theorem prob_eq_avg (m l t : ℕ) (P : (Fin t → Finset ℕ) → Prop) [DecidablePred P] :
    prob m l t P = avg m l t (fun B => if P B then (1:ℝ) else 0) := by
  classical
  simp [prob,avg]
  congr 3
  ext B
  simp

theorem finite_chebyshev (m l t : ℕ) (hm : t*l ≤ m)
    (X : (Fin t → Finset ℕ) → ℝ) (T : ℝ) (hT : 0 < T) :
    prob m l t (fun B => T ≤ |X B-avg m l t X|) ≤ cov m l t X X/T^2 := by
  classical
  have hp (B : Fin t → Finset ℕ) :
      T^2*(if T ≤ |X B-avg m l t X| then (1:ℝ) else 0) ≤ (X B-avg m l t X)^2 := by
    by_cases h : T ≤ |X B-avg m l t X|
    · simp only [if_pos h,mul_one]
      simpa only [sq_abs] using (sq_le_sq₀ (le_of_lt hT) (abs_nonneg _)).mpr h
    · simp only [if_neg h,mul_zero]
      exact sq_nonneg _
  have h := avg_mono m l t _ _ (fun B _ => hp B)
  rw [avg_smul,centered_square m l t hm,← prob_eq_avg] at h
  apply (le_div_iff₀ (sq_pos_of_pos hT)).mpr
  nlinarith

theorem variance_bound_of_covariance (m l t : ℕ) (G : Finset (Finset ℕ))
    (i j : Fin t) (hij : i ≠ j)
    (hc : cov m l t (etaI G i) (etaI G j) ≤
      avg m l t (etaI G i)*(1-avg m l t (etaI G i))/((t:ℝ)-1)) :
    cov m l t (fun B => (eta G B : ℝ)) (fun B => (eta G B : ℝ)) ≤
      2*(t:ℝ)*(avg m l t (etaI G i)*(1-avg m l t (etaI G i))) := by
  have ht : 2 ≤ t := by
    have hi := i.isLt
    have hj := j.isLt
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    omega
  have htr : (2:ℝ) ≤ t := by exact_mod_cast ht
  have hd : 0 < (t:ℝ)-1 := by linarith
  have hc' := (le_div_iff₀ hd).mp hc
  rw [variance_eta m l t G i j hij]
  have hmul := mul_le_mul_of_nonneg_left hc' (show 0 ≤ (t:ℝ) by positivity)
  nlinarith

theorem concentration_of_covariance (m l t : ℕ) (hm : t*l ≤ m)
    (G : Finset (Finset ℕ)) (i j : Fin t) (hij : i ≠ j)
    (hc : cov m l t (etaI G i) (etaI G j) ≤
      avg m l t (etaI G i)*(1-avg m l t (etaI G i))/((t:ℝ)-1))
    (β : ℝ) (hβ : 0 < β) :
    prob m l t (fun B => |(eta G B : ℝ)-(t:ℝ)*avg m l t (etaI G i)| ≥ β*t) ≤
      2*avg m l t (etaI G i)*(1-avg m l t (etaI G i))/(β^2*t) := by
  have ht : 0 < t := Nat.zero_lt_of_lt i.isLt
  have htr : (0:ℝ) < t := by exact_mod_cast ht
  have h := finite_chebyshev m l t hm (fun B => (eta G B : ℝ)) (β*t) (mul_pos hβ htr)
  rw [avg_eta m l t G i] at h
  apply h.trans
  calc
    _ ≤ (2*(t:ℝ)*(avg m l t (etaI G i)*(1-avg m l t (etaI G i))))/(β*t)^2 :=
      div_le_div_of_nonneg_right (variance_bound_of_covariance m l t G i j hij hc) (sq_nonneg _)
    _ = _ := by field_simp <;> ring

end FranklKupavskii2022.EMC.Exchange

namespace FranklKupavskii2022.EMC.Exchange
open Finset
set_option maxHeartbeats 1000000

theorem ground_permutation {α : Type*} [DecidableEq α] (Y A C : Finset α)
    (hA : A ⊆ Y) (hC : C ⊆ Y) (hc : A.card=C.card) :
    ∃ e : Equiv.Perm α, (∀ x, e x ∈ Y ↔ x ∈ Y) ∧ A.map e.toEmbedding = C := by
  classical
  let A' := A.subtype (fun x => x ∈ Y)
  let C' := C.subtype (fun x => x ∈ Y)
  have hAc : A'.card=A.card := by
    simp only [A',card_subtype,filter_true_of_mem (fun x hx => hA hx)]
  have hCc : C'.card=C.card := by
    simp only [C',card_subtype,filter_true_of_mem (fun x hx => hC hx)]
  obtain ⟨e,he⟩ := Equiv.Perm.exists_map_finset_eq A' C' (hAc.trans (hc.trans hCc.symm))
  let E : Equiv.Perm α := e.extendDomain (Equiv.refl {x // x ∈ Y})
  have hE (x : {x // x ∈ Y}) : E x = (e x : α) := by
    exact Equiv.Perm.extendDomain_apply_subtype e (Equiv.refl _) x.property
  refine ⟨E,?_,?_⟩
  · intro x
    by_cases hx : x ∈ Y
    · have hh : E x ∈ Y := by simpa only [hE ⟨x,hx⟩] using (e ⟨x,hx⟩).property
      simp only [hh,hx]
    · have hh : E x = x := Equiv.Perm.extendDomain_apply_not_subtype e (Equiv.refl _) hx
      simp only [hh]
  · calc
      A.map E.toEmbedding = (A'.map (Function.Embedding.subtype _)).map E.toEmbedding := by
        rw [subtype_map_of_mem (fun x hx => hA hx)]
      _ = (A'.map e.toEmbedding).map (Function.Embedding.subtype _) := by
        rw [map_map,map_map]
        congr 1
        ext x
        exact hE x
      _ = C := by rw [he,subtype_map_of_mem (fun x hx => hC hx)]

def groundMap {t : ℕ} (e : Equiv.Perm ℕ) (B : Fin t → Finset ℕ) : Fin t → Finset ℕ :=
  fun i => (B i).map e.toEmbedding

theorem groundMap_inverse {t : ℕ} (e : Equiv.Perm ℕ) (B : Fin t → Finset ℕ) :
    groundMap e.symm (groundMap e B) = B := by
  funext i
  simp [groundMap,map_map]

theorem groundMap_mem {m l t : ℕ} (e : Equiv.Perm ℕ)
    (he : ∀ x, e x ∈ Icc 1 m ↔ x ∈ Icc 1 m)
    {B : Fin t → Finset ℕ} (hB : B ∈ tMatchings m l t) :
    groundMap e B ∈ tMatchings m l t := by
  rw [mem_matching] at hB ⊢
  constructor
  · intro i
    constructor
    · intro x hx
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      exact (he a).mpr ((hB.1 i).1 ha)
    · simpa [groundMap] using (hB.1 i).2
  · intro i j hij
    simpa only [groundMap,disjoint_map] using hB.2 i j hij

theorem avg_groundMap (m l t : ℕ) (e : Equiv.Perm ℕ)
    (he : ∀ x, e x ∈ Icc 1 m ↔ x ∈ Icc 1 m)
    (X : (Fin t → Finset ℕ) → ℝ) :
    avg m l t (fun B => X (groundMap e B)) = avg m l t X := by
  have hei (x : ℕ) : e.symm x ∈ Icc 1 m ↔ x ∈ Icc 1 m := by
    simpa using (he (e.symm x)).symm
  unfold avg
  congr 1
  apply sum_bij (fun B _ => groundMap e B)
  · intro B hB
    exact groundMap_mem e he hB
  · intro B hB C hC h
    have hh := congrArg (groundMap e.symm) h
    simpa only [groundMap_inverse] using hh
  · intro B hB
    refine ⟨groundMap e.symm B,groundMap_mem e.symm hei hB,?_⟩
    simpa using groundMap_inverse e.symm B
  · intros
    rfl

end FranklKupavskii2022.EMC.Exchange

namespace FranklKupavskii2022.EMC.Exchange
open Finset
set_option maxHeartbeats 1000000

theorem avg_congr (m l t : ℕ) (X Y : (Fin t → Finset ℕ) → ℝ)
    (h : ∀ B ∈ tMatchings m l t, X B=Y B) : avg m l t X = avg m l t Y := by
  unfold avg
  rw [sum_congr rfl h]

theorem avg_finset_sum {α : Type*} (m l t : ℕ) (s : Finset α)
    (X : α → (Fin t → Finset ℕ) → ℝ) :
    avg m l t (fun B => ∑ a ∈ s, X a B) = ∑ a ∈ s, avg m l t (X a) := by
  unfold avg
  rw [sum_comm,sum_div]

theorem avg_fiber_eq (m l t : ℕ) (i : Fin t) (A C : Finset ℕ)
    (hA : A ∈ (Icc 1 m).powersetCard l) (hC : C ∈ (Icc 1 m).powersetCard l) :
    avg m l t (fun B => if B i=A then (1:ℝ) else 0) =
      avg m l t (fun B => if B i=C then (1:ℝ) else 0) := by
  classical
  obtain ⟨e,he,heA⟩ := ground_permutation (Icc 1 m) A C
    (mem_powersetCard.mp hA).1 (mem_powersetCard.mp hC).1
    ((mem_powersetCard.mp hA).2.trans (mem_powersetCard.mp hC).2.symm)
  have h := avg_groundMap m l t e he (fun B => if B i=C then (1:ℝ) else 0)
  have hev (B : Fin t → Finset ℕ) : groundMap e B i=C ↔ B i=A := by
    rw [← heA]
    exact (Finset.map_injective e.toEmbedding).eq_iff
  simpa only [hev] using h

theorem avg_indicator_density (m l t : ℕ) (hm : t*l ≤ m)
    (G : Finset (Finset ℕ)) (hG : G ⊆ (Icc 1 m).powersetCard l) (i : Fin t) :
    avg m l t (etaI G i) = density m l G := by
  classical
  let T := (Icc 1 m).powersetCard l
  let A := blocks l t i
  have hA : A ∈ T := by
    exact mem_powersetCard.mpr (((mem_matching _).mp (blocks_mem m l t hm)).1 i)
  let p := avg m l t (fun B => if B i=A then (1:ℝ) else 0)
  have hp (C : Finset ℕ) (hC : C ∈ T) :
      avg m l t (fun B => if B i=C then (1:ℝ) else 0) = p :=
    avg_fiber_eq m l t i C A hC hA
  have hnorm : (T.card:ℝ)*p = 1 := by
    calc
      _ = ∑ C ∈ T, avg m l t (fun B => if B i=C then (1:ℝ) else 0) := by
        symm
        calc
          _ = ∑ _C ∈ T, p := sum_congr rfl (fun C hC => hp C hC)
          _ = _ := by simp
      _ = avg m l t (fun B => ∑ C ∈ T, if B i=C then (1:ℝ) else 0) :=
        (avg_finset_sum m l t T _).symm
      _ = avg m l t (fun _ => (1:ℝ)) := by
        apply avg_congr
        intro B hB
        have hBi : B i ∈ T := mem_powersetCard.mpr (((mem_matching _).mp hB).1 i)
        simp [hBi]
      _ = 1 := avg_const m l t hm 1
  have hcard : T.card=m.choose l := by simp [T,card_powersetCard]
  have hn : (T.card:ℝ) ≠ 0 := by intro h; rw [h,zero_mul] at hnorm; norm_num at hnorm
  calc
    _ = avg m l t (fun B => ∑ C ∈ G, if B i=C then (1:ℝ) else 0) := by
      apply avg_congr
      intro B _
      simp [etaI]
    _ = ∑ C ∈ G, avg m l t (fun B => if B i=C then (1:ℝ) else 0) := avg_finset_sum m l t G _
    _ = (G.card:ℝ)*p := by
      calc
        _ = ∑ _C ∈ G, p := sum_congr rfl (fun C hC => hp C (hG hC))
        _ = _ := by simp
    _ = (G.card:ℝ)/(T.card:ℝ) := by
      apply (eq_div_iff hn).mpr
      nlinarith [hnorm]
    _ = density m l G := by rw [hcard]; rfl

theorem avg_eta_density (m l t : ℕ) (hm : t*l ≤ m)
    (G : Finset (Finset ℕ)) (hG : G ⊆ (Icc 1 m).powersetCard l) (i : Fin t) :
    avg m l t (fun B => (eta G B : ℝ)) = (t:ℝ)*density m l G := by
  rw [avg_eta m l t G i,avg_indicator_density m l t hm G hG i]

theorem covariance_density_lower_bound (m l t : ℕ) (hm : t*l ≤ m)
    (G : Finset (Finset ℕ)) (hG : G ⊆ (Icc 1 m).powersetCard l)
    (i j : Fin t) (hij : i ≠ j) :
    -(density m l G*(1-density m l G))/((t:ℝ)-1) ≤ cov m l t (etaI G i) (etaI G j) := by
  simpa only [avg_indicator_density m l t hm G hG i] using
    covariance_lower_bound m l t hm G i j hij

end FranklKupavskii2022.EMC.Exchange

namespace FranklKupavskii2022.EMC.Exchange
open Finset
set_option maxHeartbeats 1000000

theorem covariance_bound_iff_upper (m l t : ℕ) (hm : t*l ≤ m)
    (G : Finset (Finset ℕ)) (hG : G ⊆ (Icc 1 m).powersetCard l)
    (i j : Fin t) (hij : i ≠ j) :
    |cov m l t (etaI G i) (etaI G j)| ≤ density m l G*(1-density m l G)/((t:ℝ)-1) ↔
      cov m l t (etaI G i) (etaI G j) ≤ density m l G*(1-density m l G)/((t:ℝ)-1) := by
  constructor
  · exact fun h => (abs_le.mp h).2
  · intro h
    apply abs_le.mpr
    refine ⟨?_,h⟩
    simpa only [neg_div] using covariance_density_lower_bound m l t hm G hG i j hij

theorem density_concentration_of_upper (m l t : ℕ) (hm : t*l ≤ m)
    (G : Finset (Finset ℕ)) (hG : G ⊆ (Icc 1 m).powersetCard l)
    (i j : Fin t) (hij : i ≠ j)
    (hc : cov m l t (etaI G i) (etaI G j) ≤ density m l G*(1-density m l G)/((t:ℝ)-1))
    (β : ℝ) (hβ : 0 < β) :
    prob m l t (fun B => |(eta G B : ℝ)-density m l G*t| ≥ β*t) ≤
      2*density m l G*(1-density m l G)/(β^2*t) := by
  have hp := avg_indicator_density m l t hm G hG i
  have hc' : cov m l t (etaI G i) (etaI G j) ≤
      avg m l t (etaI G i)*(1-avg m l t (etaI G i))/((t:ℝ)-1) := by simpa only [hp] using hc
  simpa only [hp,mul_comm (t:ℝ) (density m l G)] using
    concentration_of_covariance m l t hm G i j hij hc' β hβ

end FranklKupavskii2022.EMC.Exchange

namespace FranklKupavskii2022.EMC.Exchange
open Finset
set_option maxHeartbeats 1000000

/-- A finite-set transport can fix the entire complement of its ground set. -/
theorem ground_permutation_fixed {α : Type*} [DecidableEq α] (Y A C : Finset α)
    (hA : A ⊆ Y) (hC : C ⊆ Y) (hc : A.card=C.card) :
    ∃ e : Equiv.Perm α, (∀ x, e x ∈ Y ↔ x ∈ Y) ∧ A.map e.toEmbedding = C ∧
      ∀ x ∉ Y, e x = x := by
  classical
  let A' := A.subtype (fun x => x ∈ Y)
  let C' := C.subtype (fun x => x ∈ Y)
  have hAc : A'.card=A.card := by
    simp only [A',card_subtype,filter_true_of_mem (fun x hx => hA hx)]
  have hCc : C'.card=C.card := by
    simp only [C',card_subtype,filter_true_of_mem (fun x hx => hC hx)]
  obtain ⟨e,he⟩ := Equiv.Perm.exists_map_finset_eq A' C' (hAc.trans (hc.trans hCc.symm))
  let E : Equiv.Perm α := e.extendDomain (Equiv.refl {x // x ∈ Y})
  have hE (x : {x // x ∈ Y}) : E x = (e x : α) :=
    Equiv.Perm.extendDomain_apply_subtype e (Equiv.refl _) x.property
  refine ⟨E,?_,?_,?_⟩
  · intro x
    by_cases hx : x ∈ Y
    · have hh : E x ∈ Y := by simpa only [hE ⟨x,hx⟩] using (e ⟨x,hx⟩).property
      simp only [hh,hx]
    · have hh : E x = x := Equiv.Perm.extendDomain_apply_not_subtype e (Equiv.refl _) hx
      simp only [hh]
  · calc
      A.map E.toEmbedding = (A'.map (Function.Embedding.subtype _)).map E.toEmbedding := by
        rw [subtype_map_of_mem (fun x hx => hA hx)]
      _ = (A'.map e.toEmbedding).map (Function.Embedding.subtype _) := by
        rw [map_map,map_map]
        congr 1
        ext x
        exact hE x
      _ = C := by rw [he,subtype_map_of_mem (fun x hx => hC hx)]
  · intro x hx
    exact Equiv.Perm.extendDomain_apply_not_subtype e (Equiv.refl _) hx

/-- Ordered disjoint pairs of equally sized sets form one ground-permutation orbit. -/
theorem ground_pair_permutation {α : Type*} [DecidableEq α]
    (Y A B C D : Finset α) (hA : A ⊆ Y) (hB : B ⊆ Y) (hC : C ⊆ Y) (hD : D ⊆ Y)
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hAC : A.card=C.card) (hBD : B.card=D.card) :
    ∃ e : Equiv.Perm α, (∀ x, e x ∈ Y ↔ x ∈ Y) ∧
      A.map e.toEmbedding=C ∧ B.map e.toEmbedding=D := by
  classical
  obtain ⟨e,he,heA,_⟩ := ground_permutation_fixed Y A C hA hC hAC
  have hCB : Disjoint C (B.map e.toEmbedding) := by
    rw [← heA]
    exact (disjoint_map e.toEmbedding).mpr hAB
  have hB' : B.map e.toEmbedding ⊆ Y \ C := by
    intro x hx
    refine mem_sdiff.mpr ⟨?_,?_⟩
    · obtain ⟨b,hb,rfl⟩ := mem_map.mp hx
      exact (he b).mpr (hB hb)
    · intro hc
      exact disjoint_left.mp hCB hc hx
  have hD' : D ⊆ Y \ C := by
    intro x hx
    exact mem_sdiff.mpr ⟨hD hx, fun hc => disjoint_left.mp hCD hc hx⟩
  obtain ⟨f,hf,hfB,hfix⟩ := ground_permutation_fixed (Y \ C) (B.map e.toEmbedding) D
    hB' hD' (by simpa using hBD)
  have hfC (x) (hx : x ∈ C) : f x=x := hfix x (by simp [hx])
  have hfY (x) : f x ∈ Y ↔ x ∈ Y := by
    by_cases hc : x ∈ C
    · rw [hfC x hc]
    by_cases hy : x ∈ Y
    · exact ⟨fun _ => hy,fun _ => (mem_sdiff.mp ((hf x).mpr (mem_sdiff.mpr ⟨hy,hc⟩))).1⟩
    · rw [hfix x (by simp [hy])]
  have hmapC : C.map f.toEmbedding=C := by
    ext x
    constructor
    · intro hx
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      change f a ∈ C
      rw [hfC a ha]
      exact ha
    · intro hx
      exact mem_map.mpr ⟨x,hx,hfC x hx⟩
  refine ⟨e.trans f,?_,?_,?_⟩
  · intro x
    exact (hfY (e x)).trans (he x)
  · calc
      A.map (e.trans f).toEmbedding = (A.map e.toEmbedding).map f.toEmbedding := by rw [map_map]; rfl
      _ = C := by rw [heA,hmapC]
  · calc
      B.map (e.trans f).toEmbedding = (B.map e.toEmbedding).map f.toEmbedding := by rw [map_map]; rfl
      _ = D := hfB

#print axioms ground_pair_permutation
end FranklKupavskii2022.EMC.Exchange

namespace FranklKupavskii2022.EMC.Exchange
open Finset
set_option maxHeartbeats 1000000

/-- Ordered disjoint pairs; for zero-size sets the diagonal empty pair is allowed. -/
def disjointPairs (G : Finset (Finset ℕ)) : Finset (Finset ℕ × Finset ℕ) :=
  (G ×ˢ G).filter (fun p => Disjoint p.1 p.2)

@[simp] theorem mem_disjointPairs (G : Finset (Finset ℕ)) (p : Finset ℕ × Finset ℕ) :
    p ∈ disjointPairs G ↔ p.1 ∈ G ∧ p.2 ∈ G ∧ Disjoint p.1 p.2 := by
  simp [disjointPairs,and_assoc]

theorem matching_pair_mem (m l t : ℕ) (i j : Fin t) (hij : i ≠ j)
    (B : Fin t → Finset ℕ) (hB : B ∈ tMatchings m l t) :
    (B i,B j) ∈ disjointPairs ((Icc 1 m).powersetCard l) := by
  have hb := (mem_matching _).mp hB
  exact (mem_disjointPairs _ _).mpr ⟨mem_powersetCard.mpr (hb.1 i),
    mem_powersetCard.mpr (hb.1 j), hb.2 i j hij⟩

theorem avg_pair_fiber_eq (m l t : ℕ) (i j : Fin t)
    (A C : Finset ℕ × Finset ℕ)
    (hA : A ∈ disjointPairs ((Icc 1 m).powersetCard l))
    (hC : C ∈ disjointPairs ((Icc 1 m).powersetCard l)) :
    avg m l t (fun B => if (B i,B j)=A then (1:ℝ) else 0) =
      avg m l t (fun B => if (B i,B j)=C then (1:ℝ) else 0) := by
  classical
  obtain ⟨hA1,hA2,hAd⟩ := (mem_disjointPairs _ _).mp hA
  obtain ⟨hC1,hC2,hCd⟩ := (mem_disjointPairs _ _).mp hC
  obtain ⟨e,he,he1,he2⟩ := ground_pair_permutation (Icc 1 m) A.1 A.2 C.1 C.2
    (mem_powersetCard.mp hA1).1 (mem_powersetCard.mp hA2).1
    (mem_powersetCard.mp hC1).1 (mem_powersetCard.mp hC2).1 hAd hCd
    ((mem_powersetCard.mp hA1).2.trans (mem_powersetCard.mp hC1).2.symm)
    ((mem_powersetCard.mp hA2).2.trans (mem_powersetCard.mp hC2).2.symm)
  have h := avg_groundMap m l t e he (fun B => if (B i,B j)=C then (1:ℝ) else 0)
  have hev (B : Fin t → Finset ℕ) : (groundMap e B i,groundMap e B j)=C ↔ (B i,B j)=A := by
    rw [Prod.ext_iff,Prod.ext_iff]
    change (B i).map e.toEmbedding=C.1 ∧ (B j).map e.toEmbedding=C.2 ↔ _
    rw [←he1,←he2,(Finset.map_injective e.toEmbedding).eq_iff,
      (Finset.map_injective e.toEmbedding).eq_iff]
  simpa only [hev] using h

/-- Any event on two distinct positions has the uniform ordered-disjoint-pair law. -/
theorem avg_pair_event (m l t : ℕ) (hm : t*l ≤ m) (i j : Fin t) (hij : i ≠ j)
    (H : Finset (Finset ℕ × Finset ℕ))
    (hH : H ⊆ disjointPairs ((Icc 1 m).powersetCard l)) :
    avg m l t (fun B => if (B i,B j) ∈ H then (1:ℝ) else 0) =
      (H.card:ℝ)/(disjointPairs ((Icc 1 m).powersetCard l)).card := by
  classical
  let P := disjointPairs ((Icc 1 m).powersetCard l)
  let A := (blocks l t i,blocks l t j)
  have hA : A ∈ P := matching_pair_mem m l t i j hij _ (blocks_mem m l t hm)
  let p := avg m l t (fun B => if (B i,B j)=A then (1:ℝ) else 0)
  have hp (C) (hC : C ∈ P) :
      avg m l t (fun B => if (B i,B j)=C then (1:ℝ) else 0)=p :=
    avg_pair_fiber_eq m l t i j C A hC hA
  have hnorm : (P.card:ℝ)*p=1 := by
    calc
      _ = ∑ C ∈ P, avg m l t (fun B => if (B i,B j)=C then (1:ℝ) else 0) := by
        symm
        calc
          _ = ∑ _C ∈ P, p := sum_congr rfl (fun C hC => hp C hC)
          _ = _ := by simp
      _ = avg m l t (fun B => ∑ C ∈ P, if (B i,B j)=C then (1:ℝ) else 0) :=
        (avg_finset_sum m l t P _).symm
      _ = avg m l t (fun _ => (1:ℝ)) := by
        apply avg_congr
        intro B hB
        have hb : (B i,B j) ∈ P := matching_pair_mem m l t i j hij B hB
        simp [hb]
      _ = 1 := avg_const m l t hm 1
  have hn : (P.card:ℝ) ≠ 0 := by intro h; rw [h,zero_mul] at hnorm; norm_num at hnorm
  calc
    _ = avg m l t (fun B => ∑ C ∈ H, if (B i,B j)=C then (1:ℝ) else 0) := by
      apply avg_congr
      intro B _
      simp
    _ = ∑ C ∈ H, avg m l t (fun B => if (B i,B j)=C then (1:ℝ) else 0) :=
      avg_finset_sum m l t H _
    _ = (H.card:ℝ)*p := by
      calc
        _ = ∑ _C ∈ H, p := sum_congr rfl (fun C hC => hp C (hH hC))
        _ = _ := by simp
    _ = (H.card:ℝ)/(P.card:ℝ) := by
      apply (eq_div_iff hn).mpr
      nlinarith [hnorm]

theorem avg_pair_product (m l t : ℕ) (hm : t*l ≤ m)
    (G : Finset (Finset ℕ)) (hG : G ⊆ (Icc 1 m).powersetCard l)
    (i j : Fin t) (hij : i ≠ j) :
    avg m l t (fun B => etaI G i B * etaI G j B) =
      ((disjointPairs G).card:ℝ)/(disjointPairs ((Icc 1 m).powersetCard l)).card := by
  classical
  have hH : disjointPairs G ⊆ disjointPairs ((Icc 1 m).powersetCard l) := by
    intro p hp
    obtain ⟨ha,hb,hd⟩ := (mem_disjointPairs _ _).mp hp
    exact (mem_disjointPairs _ _).mpr ⟨hG ha,hG hb,hd⟩
  rw [← avg_pair_event m l t hm i j hij (disjointPairs G) hH]
  apply avg_congr
  intro B hB
  have hd := ((mem_matching _).mp hB).2 i j hij
  simp only [mem_disjointPairs,hd,and_true]
  unfold etaI
  split_ifs <;> simp_all

theorem covariance_disjoint_pairs (m l t : ℕ) (hm : t*l ≤ m)
    (G : Finset (Finset ℕ)) (hG : G ⊆ (Icc 1 m).powersetCard l)
    (i j : Fin t) (hij : i ≠ j) :
    cov m l t (etaI G i) (etaI G j) =
      ((disjointPairs G).card:ℝ)/(disjointPairs ((Icc 1 m).powersetCard l)).card -
      density m l G ^ 2 := by
  unfold cov
  rw [avg_pair_product m l t hm G hG i j hij,
    avg_indicator_density m l t hm G hG i,avg_indicator_density m l t hm G hG j]
  ring

#print axioms covariance_disjoint_pairs
end FranklKupavskii2022.EMC.Exchange

namespace FranklKupavskii2022.EMC.Exchange
open Finset
set_option maxHeartbeats 1000000

theorem disjoint_powersetCard (Y A : Finset ℕ) (l : ℕ) :
    (Y.powersetCard l).filter (fun B => Disjoint A B) = (Y \ A).powersetCard l := by
  ext B
  simp only [mem_filter,mem_powersetCard,subset_sdiff]
  constructor
  · rintro ⟨⟨hBY,hcard⟩,hd⟩
    exact ⟨⟨hBY,hd.symm⟩,hcard⟩
  · rintro ⟨⟨hBY,hd⟩,hcard⟩
    exact ⟨⟨hBY,hcard⟩,hd.symm⟩

theorem card_disjointPairs (Y : Finset ℕ) (l : ℕ) :
    (disjointPairs (Y.powersetCard l)).card = Y.card.choose l * (Y.card-l).choose l := by
  classical
  let T := Y.powersetCard l
  have hrow (A) (hA : A ∈ T) :
      (∑ B ∈ T, if Disjoint A B then (1:ℕ) else 0)=(Y.card-l).choose l := by
    have h := mem_powersetCard.mp hA
    calc
      _ = (T.filter (fun B => Disjoint A B)).card := by simp only [card_eq_sum_ones,sum_filter]
      _ = ((Y \ A).powersetCard l).card := by rw [disjoint_powersetCard]
      _ = (Y.card-l).choose l := by rw [card_powersetCard,card_sdiff_of_subset h.1,h.2]
  calc
    _ = ∑ A ∈ T, ∑ B ∈ T, if Disjoint A B then (1:ℕ) else 0 := by
      simp only [disjointPairs,card_eq_sum_ones,sum_filter,sum_product,T]
    _ = ∑ _A ∈ T, (Y.card-l).choose l := sum_congr rfl (fun A hA => hrow A hA)
    _ = Y.card.choose l * (Y.card-l).choose l := by simp [T,card_powersetCard]

theorem avg_pair_product_choose (m l t : ℕ) (hm : t*l ≤ m)
    (G : Finset (Finset ℕ)) (hG : G ⊆ (Icc 1 m).powersetCard l)
    (i j : Fin t) (hij : i ≠ j) :
    avg m l t (fun B => etaI G i B * etaI G j B) =
      ((disjointPairs G).card:ℝ)/((m.choose l:ℝ)*((m-l).choose l:ℝ)) := by
  rw [avg_pair_product m l t hm G hG i j hij,card_disjointPairs]
  simp

theorem covariance_disjoint_pairs_choose (m l t : ℕ) (hm : t*l ≤ m)
    (G : Finset (Finset ℕ)) (hG : G ⊆ (Icc 1 m).powersetCard l)
    (i j : Fin t) (hij : i ≠ j) :
    cov m l t (etaI G i) (etaI G j) =
      ((disjointPairs G).card:ℝ)/((m.choose l:ℝ)*((m-l).choose l:ℝ)) -
      density m l G ^ 2 := by
  rw [covariance_disjoint_pairs m l t hm G hG i j hij,card_disjointPairs]
  simp

/-- The remaining probabilistic covariance obligation is exactly a finite edge-count inequality. -/
theorem covariance_bound_iff_pair_count (m l t : ℕ) (hm : t*l ≤ m)
    (G : Finset (Finset ℕ)) (hG : G ⊆ (Icc 1 m).powersetCard l)
    (i j : Fin t) (hij : i ≠ j) :
    |cov m l t (etaI G i) (etaI G j)| ≤ density m l G*(1-density m l G)/((t:ℝ)-1) ↔
    ((disjointPairs G).card:ℝ)/((m.choose l:ℝ)*((m-l).choose l:ℝ)) ≤
      density m l G ^ 2 + density m l G*(1-density m l G)/((t:ℝ)-1) := by
  rw [covariance_bound_iff_upper m l t hm G hG i j hij,
    covariance_disjoint_pairs_choose m l t hm G hG i j hij]
  exact sub_le_iff_le_add'

#print axioms covariance_bound_iff_pair_count
end FranklKupavskii2022.EMC.Exchange

namespace FranklKupavskii2022.EMC.Exchange
open Finset
set_option maxHeartbeats 1000000

/-- The empty-set diagonal remains present at l=0. -/
theorem zero_size_pair_count (Y : Finset ℕ) : (disjointPairs (Y.powersetCard 0)).card=1 := by
  rw [card_disjointPairs]
  simp

theorem singleton_nonempty_pair_count (A : Finset ℕ) (hA : A ≠ ∅) :
    (disjointPairs {A}).card=0 := by
  simp [disjointPairs,hA]

theorem empty_family_covariance (m l t : ℕ) (i j : Fin t) :
    cov m l t (etaI ∅ i) (etaI ∅ j)=0 := by
  simp [cov,etaI,avg]

/-- Six oriented edges, rather than three unoriented edges, on complementary 2-subsets. -/
theorem four_point_pair_count : (disjointPairs ((Icc 1 4).powersetCard 2)).card=6 := by
  rw [card_disjointPairs]
  norm_num [Nat.choose]

/-- The two-position boundary needs only the elementary Bernoulli product bound. -/
theorem two_position_covariance_bound (m l : ℕ) (hm : 2*l ≤ m)
    (G : Finset (Finset ℕ)) (hG : G ⊆ (Icc 1 m).powersetCard l)
    (i j : Fin 2) (hij : i ≠ j) :
    |cov m l 2 (etaI G i) (etaI G j)| ≤ density m l G*(1-density m l G) := by
  have hp : avg m l 2 (fun B => etaI G i B*etaI G j B) ≤ density m l G := by
    rw [← avg_indicator_density m l 2 hm G hG i]
    apply avg_mono
    intro B _
    unfold etaI
    split_ifs <;> norm_num
  have hu : cov m l 2 (etaI G i) (etaI G j) ≤ density m l G*(1-density m l G) := by
    unfold cov
    rw [avg_indicator_density m l 2 hm G hG i,avg_indicator_density m l 2 hm G hG j]
    nlinarith
  have hh := (covariance_bound_iff_upper m l 2 hm G hG i j hij).mpr
    (by norm_num; exact hu)
  norm_num at hh
  exact hh

end FranklKupavskii2022.EMC.Exchange

namespace FranklKupavskii2022.EMC.Kneser
open Finset
set_option maxHeartbeats 1000000

/-- The unnormalized disjointness operator, including the empty-set diagonal when l=0. -/
noncomputable def K (Y : Finset ℕ) (l : ℕ) (f : Finset ℕ → ℝ) (A : Finset ℕ) : ℝ :=
  ∑ B ∈ Y.powersetCard l, if Disjoint A B then f B else 0

noncomputable def incidence (R A : Finset ℕ) : ℝ := if R ⊆ A then 1 else 0

theorem K_add (Y : Finset ℕ) (l : ℕ) (f g : Finset ℕ → ℝ) (A : Finset ℕ) :
    K Y l (fun B => f B + g B) A = K Y l f A + K Y l g A := by
  classical
  simp only [K, ← sum_add_distrib]
  apply sum_congr rfl
  intro B hB
  split_ifs <;> ring

theorem K_smul (Y : Finset ℕ) (l : ℕ) (c : ℝ) (f : Finset ℕ → ℝ) (A : Finset ℕ) :
    K Y l (fun B => c * f B) A = c * K Y l f A := by
  classical
  simp only [K, mul_sum]
  apply sum_congr rfl
  intro B hB
  split_ifs <;> ring

theorem K_symmetric (Y : Finset ℕ) (l : ℕ) (f g : Finset ℕ → ℝ) :
    ∑ A ∈ Y.powersetCard l, f A * K Y l g A =
    ∑ A ∈ Y.powersetCard l, K Y l f A * g A := by
  classical
  simp only [K, mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro A hA
  apply sum_congr rfl
  intro B hB
  by_cases hd : Disjoint A B
  · simp [hd, hd.symm, mul_comm]
  · have hd' : ¬ Disjoint B A := fun h => hd h.symm
    simp [hd, hd']

theorem disjoint_filter (Y A : Finset ℕ) (l : ℕ) :
    (Y.powersetCard l).filter (fun B => Disjoint A B) = (Y \ A).powersetCard l := by
  ext B
  simp only [mem_filter, mem_powersetCard, subset_sdiff]
  constructor
  · rintro ⟨⟨h, hc⟩, hd⟩; exact ⟨⟨h, hd.symm⟩, hc⟩
  · rintro ⟨⟨h, hd⟩, hc⟩; exact ⟨⟨h, hc⟩, hd.symm⟩

theorem K_incidence (Y A R : Finset ℕ) (l : ℕ)
    (hA : A ∈ Y.powersetCard l) (hR : R ⊆ Y) (hr : R.card ≤ l) :
    K Y l (incidence R) A =
      ((Y.card - l - R.card).choose (l - R.card) : ℝ) * (if Disjoint A R then 1 else 0) := by
  classical
  unfold K incidence
  rw [← sum_filter, disjoint_filter]
  by_cases hd : Disjoint A R
  · have hs : R ⊆ Y \ A := subset_sdiff.mpr ⟨hR, hd.symm⟩
    simp only [hd, ite_true, mul_one]
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    rw [card_filter_powersetCard_subset R (Y \ A) l hs hr,
      card_sdiff_of_subset (mem_powersetCard.mp hA).1, (mem_powersetCard.mp hA).2]
  · simp only [hd, ite_false, mul_zero]
    apply sum_eq_zero
    intro B hB
    have hb := (mem_powersetCard.mp hB).1
    have hnot : ¬ R ⊆ B := by
      intro h
      exact hd ((disjoint_of_subset_left h (subset_sdiff.mp hb).2).symm)
    simp [hnot]

/-- Inclusion-exclusion on R∩A expresses disjointness in the inclusion basis. -/
theorem disjoint_inclusion_exclusion (A R : Finset ℕ) :
    (if Disjoint A R then (1 : ℝ) else 0) =
      ∑ S ∈ R.powerset, (-1 : ℝ) ^ S.card * incidence S A := by
  classical
  have hf : R.powerset.filter (fun S => S ⊆ A) = (R ∩ A).powerset := by
    ext S
    simp only [mem_filter, mem_powerset, subset_inter_iff]
  have he := sum_powerset_neg_one_pow_card (x := R ∩ A)
  have her : (∑ S ∈ (R ∩ A).powerset, (-1 : ℝ) ^ S.card) =
      if R ∩ A = ∅ then 1 else 0 := by exact_mod_cast he
  simp only [incidence, mul_ite, mul_one, mul_zero]
  rw [← sum_filter, hf, her]
  by_cases hd : Disjoint A R
  · simp [hd, disjoint_iff_inter_eq_empty.mp hd.symm]
  · have hn : R ∩ A ≠ ∅ := fun h => hd (disjoint_iff_inter_eq_empty.mpr h).symm
    simp [hd, hn]

theorem K_incidence_triangular (Y A R : Finset ℕ) (l : ℕ)
    (hA : A ∈ Y.powersetCard l) (hR : R ⊆ Y) (hr : R.card ≤ l) :
    K Y l (incidence R) A =
      ((Y.card - l - R.card).choose (l - R.card) : ℝ) *
        ∑ S ∈ R.powerset, (-1 : ℝ) ^ S.card * incidence S A := by
  rw [K_incidence Y A R l hA hR hr, disjoint_inclusion_exclusion]

/-- The top inclusion level spans every function on the l-slice, without a dimension count. -/
theorem incidence_resolution (Y A : Finset ℕ) (l : ℕ) (f : Finset ℕ → ℝ)
    (hA : A ∈ Y.powersetCard l) :
    ∑ R ∈ Y.powersetCard l, f R * incidence R A = f A := by
  classical
  calc
    _ = f A * incidence A A := by
      apply sum_eq_single A
      · intro R hR hRA
        have hn : ¬ R ⊆ A := by
          intro hs
          have hc : R.card = A.card := (mem_powersetCard.mp hR).2.trans (mem_powersetCard.mp hA).2.symm
          exact hRA (eq_of_subset_of_card_le hs hc.ge)
        simp [incidence, hn]
      · exact fun hn => False.elim (hn hA)
    _ = f A := by simp [incidence]

end FranklKupavskii2022.EMC.Kneser

namespace FranklKupavskii2022.EMC.Kneser
open Finset
set_option maxHeartbeats 1000000

noncomputable def moment (Y : Finset ℕ) (l : ℕ) (R : Finset ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  ∑ A ∈ Y.powersetCard l, incidence R A * f A

noncomputable def eigenvalue (Y : Finset ℕ) (l r : ℕ) : ℝ :=
  (-1 : ℝ) ^ r * ((Y.card - l - r).choose (l - r) : ℝ)

theorem moment_action (Y R : Finset ℕ) (l : ℕ) (f : Finset ℕ → ℝ)
    (hR : R ⊆ Y) (hr : R.card ≤ l) :
    moment Y l R (K Y l f) = ((Y.card-l-R.card).choose (l-R.card) : ℝ) *
      ∑ S ∈ R.powerset, (-1 : ℝ) ^ S.card * moment Y l S f := by
  classical
  unfold moment
  rw [K_symmetric]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro A hA
  rw [K_incidence_triangular Y A R l hA hR hr]
  simp only [sum_mul, mul_sum]
  apply sum_congr rfl
  intro S hS
  ring

theorem moment_of_eigenfunction (Y R : Finset ℕ) (l : ℕ) (f : Finset ℕ → ℝ) (μ : ℝ)
    (hf : ∀ A ∈ Y.powersetCard l, K Y l f A = μ * f A) :
    moment Y l R (K Y l f) = μ * moment Y l R f := by
  classical
  unfold moment
  rw [mul_sum]
  exact sum_congr rfl (fun A hA => by rw [hf A hA]; ring)

theorem moment_top (Y A : Finset ℕ) (l : ℕ) (f : Finset ℕ → ℝ)
    (hA : A ∈ Y.powersetCard l) : moment Y l A f = f A := by
  classical
  unfold moment
  calc
    _ = incidence A A * f A := by
      apply sum_eq_single A
      · intro B hB hBA
        have hn : ¬ A ⊆ B := by
          intro hs
          have hc : B.card = A.card := (mem_powersetCard.mp hB).2.trans (mem_powersetCard.mp hA).2.symm
          exact hBA (eq_of_subset_of_card_le hs hc.le).symm
        simp [incidence, hn]
      · exact fun hn => False.elim (hn hA)
    _ = f A := by simp [incidence]

/-- Orthogonality to every smaller inclusion level isolates the diagonal coefficient. -/
theorem moment_diagonal (Y R : Finset ℕ) (l : ℕ) (f : Finset ℕ → ℝ) (μ : ℝ)
    (hR : R ⊆ Y) (hr : R.card ≤ l)
    (hf : ∀ A ∈ Y.powersetCard l, K Y l f A = μ * f A)
    (hsmall : ∀ S ⊆ R, S.card < R.card → moment Y l S f = 0) :
    (μ - eigenvalue Y l R.card) * moment Y l R f = 0 := by
  classical
  have ha := moment_action Y R l f hR hr
  rw [moment_of_eigenfunction Y R l f μ hf] at ha
  have hs : (∑ S ∈ R.powerset, (-1 : ℝ)^S.card * moment Y l S f) =
      (-1 : ℝ)^R.card * moment Y l R f := by
    apply sum_eq_single R
    · intro S hS hne
      have hsub := mem_powerset.mp hS
      have hlt : S.card < R.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hne⟩)
      rw [hsmall S hsub hlt, mul_zero]
    · simp
  rw [hs] at ha
  unfold eigenvalue
  nlinarith

/-- Every eigenvalue on the mean-zero subspace is one of the nonconstant inclusion levels.
No multiplicity formula or completeness assertion is assumed. -/
theorem centered_eigenvalue (Y : Finset ℕ) (l : ℕ) (f : Finset ℕ → ℝ) (μ : ℝ)
    (hf : ∀ A ∈ Y.powersetCard l, K Y l f A = μ * f A)
    (hmean : ∑ A ∈ Y.powersetCard l, f A = 0)
    (hne : ∃ A ∈ Y.powersetCard l, f A ≠ 0) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ l ∧ μ = eigenvalue Y l r := by
  classical
  by_contra hn
  have hμ : ∀ r : ℕ, 1 ≤ r → r ≤ l → μ ≠ eigenvalue Y l r := by
    intro r h1 hl he
    exact hn ⟨r,h1,hl,he⟩
  have hz : ∀ n : ℕ, ∀ R : Finset ℕ, R.card = n → R ⊆ Y → R.card ≤ l → moment Y l R f = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro R hcard hRY hRl
      by_cases hn0 : n = 0
      · have hR0 : R = ∅ := card_eq_zero.mp (hcard.trans hn0)
        simpa [hR0,moment,incidence] using hmean
      · have hd := moment_diagonal Y R l f μ hRY hRl hf (by
          intro S hSR hlt
          exact ih S.card (hcard ▸ hlt) S rfl (hSR.trans hRY) (le_trans (card_le_card hSR) hRl))
        exact (mul_eq_zero.mp hd).resolve_left (sub_ne_zero.mpr (hμ R.card (by omega) hRl))
  obtain ⟨A,hA,hfA⟩ := hne
  have hzero := hz A.card A rfl (mem_powersetCard.mp hA).1 (mem_powersetCard.mp hA).2.le
  rw [moment_top Y A l f hA] at hzero
  exact hfA hzero

end FranklKupavskii2022.EMC.Kneser

namespace FranklKupavskii2022.EMC.Kneser
open Finset

theorem choose_diagonal_mono (n k d : ℕ) : n.choose k ≤ (n+d).choose (k+d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    simpa only [Nat.add_succ, Nat.choose_succ_succ] using ih.trans (Nat.le_add_right _ _)

theorem eigenvalue_abs_le (Y : Finset ℕ) (l r : ℕ) (hm : 2*l ≤ Y.card)
    (hr : 1 ≤ r) (hrl : r ≤ l) :
    |eigenvalue Y l r| ≤ ((Y.card-l-1).choose (l-1) : ℝ) := by
  unfold eigenvalue
  rw [abs_mul, abs_pow]
  norm_num only [abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  have hh := choose_diagonal_mono (Y.card-l-r) (l-r) (r-1)
  have h1 : Y.card-l-r+(r-1) = Y.card-l-1 := by omega
  have h2 : l-r+(r-1) = l-1 := by omega
  rw [h1,h2] at hh
  exact_mod_cast hh

theorem centered_eigenvalue_bound (Y : Finset ℕ) (l : ℕ) (f : Finset ℕ → ℝ) (μ : ℝ)
    (hm : 2*l ≤ Y.card)
    (hf : ∀ A ∈ Y.powersetCard l, K Y l f A = μ * f A)
    (hmean : ∑ A ∈ Y.powersetCard l, f A = 0)
    (hne : ∃ A ∈ Y.powersetCard l, f A ≠ 0) :
    |μ| ≤ ((Y.card-l-1).choose (l-1) : ℝ) := by
  obtain ⟨r,hr,hrl,rfl⟩ := centered_eigenvalue Y l f μ hf hmean hne
  exact eigenvalue_abs_le Y l r hm hr hrl

theorem coefficient_degree_identity (m l : ℕ) (hl : 1 ≤ l) (hm : 2*l ≤ m) :
    ((m-l : ℕ) : ℝ) * ((m-l-1).choose (l-1) : ℝ) =
      (l : ℝ) * ((m-l).choose l : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (m-l-1) (l-1)
  have h1 : m-l-1+1 = m-l := by omega
  have h2 : l-1+1 = l := by omega
  rw [h1,h2] at h
  exact_mod_cast h.trans (Nat.mul_comm _ _)

end FranklKupavskii2022.EMC.Kneser

namespace FranklKupavskii2022.EMC.Kneser
open Finset
open scoped RealInnerProductSpace
set_option maxHeartbeats 1500000

theorem symmetric_quadratic_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ι → ℝ) (D C : ℝ)
    (hsym : ∀ i j, a i j = a j i) (hrows : ∀ i, ∑ j, a i j = D)
    (heig : ∀ (f : ι → ℝ) (μ : ℝ),
      (∀ i, ∑ j, a i j * f j = μ * f i) → (∑ i, f i = 0) → f ≠ 0 → |μ| ≤ C)
    (f : ι → ℝ) (hf : ∑ i, f i = 0) :
    |∑ i, f i * (∑ j, a i j * f j)| ≤ C * ∑ i, f i ^ 2 := by
  classical
  let E := EuclideanSpace ℝ ι
  let T : E →ₗ[ℝ] E :=
    { toFun := fun x => WithLp.toLp 2 (fun i => ∑ j, a i j * x j)
      map_add' := by intro x y; ext i; simp [E, WithLp.ofLp_add, mul_add, sum_add_distrib]
      map_smul' := by intro c x; ext i; simp [E, WithLp.ofLp_smul, mul_comm, mul_left_comm, ← mul_sum] }
  have hT (x : E) (i : ι) : T x i = ∑ j, a i j * x j := rfl
  have htotal (x : E) : ∑ i, T x i = D * ∑ i, x i := by
    simp only [hT, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    rw [← sum_mul]
    have hc : ∑ i, a i j = D := by simp_rw [hsym]; exact hrows j
    rw [hc]
  let S : Submodule ℝ E :=
    { carrier := {x | ∑ i, x i = 0}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change (∑ i, x i) = 0 at hx
        change (∑ i, y i) = 0 at hy
        simpa [E, WithLp.ofLp_add, sum_add_distrib, hx, hy]
      smul_mem' := by intro c x hx; simpa [E, WithLp.ofLp_smul, ← mul_sum] using congrArg (fun z : ℝ => c * z) hx }
  have hS (x : E) : x ∈ S ↔ ∑ i, x i = 0 := Iff.rfl
  let U : S →ₗ[ℝ] S := T.restrict (by
    intro x hx
    rw [hS, htotal, (hS x).mp hx, mul_zero])
  have hU (x : S) (i : ι) : (U x : E) i = ∑ j, a i j * (x : E) j := rfl
  have hUsym : U.IsSymmetric := by
    intro x y
    change ⟪T (x : E), (y : E)⟫ = ⟪(x : E), T (y : E)⟫
    simp only [E, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hT, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [hsym j i]
    ring
  let b := hUsym.eigenvectorBasis (n := Module.finrank ℝ S) rfl
  let ev := hUsym.eigenvalues (n := Module.finrank ℝ S) rfl
  have hbound (i : Fin (Module.finrank ℝ S)) : |ev i| ≤ C := by
    apply heig (fun j => ((b i : S) : E) j) (ev i)
    · intro j
      have hh := congrArg (fun x : S => (x : E) j) (hUsym.apply_eigenvectorBasis rfl i)
      exact hh
    · exact (hS _).mp (b i).property
    · intro hh
      have hz : b i = 0 := by
        apply Subtype.ext
        ext j
        exact congrFun hh j
      exact (hUsym.hasEigenvector_eigenvectorBasis rfl i).2 hz
  let x : S := ⟨WithLp.toLp 2 f, hf⟩
  have hx : ⟪x, U x⟫ = ∑ i, ev i * ⟪b i, x⟫ ^ 2 := by
    rw [← b.sum_inner_mul_inner x (U x)]
    apply sum_congr rfl
    intro i hi
    have ht := hUsym (b i) x
    rw [hUsym.apply_eigenvectorBasis rfl i, real_inner_smul_left] at ht
    rw [← ht, real_inner_comm x (b i)]
    dsimp [ev]
    ring
  have hb : |⟪x, U x⟫| ≤ C * ‖x‖ ^ 2 := by
    rw [hx, ← b.sum_sq_inner_right x, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro i hi
    rw [abs_mul, abs_of_nonneg (sq_nonneg ⟪b i, x⟫)]
    exact mul_le_mul_of_nonneg_right (hbound i) (sq_nonneg _)
  have hxx : ‖x‖ ^ 2 = ∑ i, f i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪(x : E), (x : E)⟫ = _
    simp only [x, E, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, WithLp.ofLp_toLp, pow_two]
  rw [hxx] at hb
  convert hb using 1
  congr 1
  change _ = ⟪(x : E), T (x : E)⟫
  simp only [E, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hT, x, WithLp.ofLp_toLp]
  apply sum_congr rfl
  intro i hi
  ring

end FranklKupavskii2022.EMC.Kneser

namespace FranklKupavskii2022.EMC.Kneser
open Finset
set_option maxHeartbeats 1500000

noncomputable def extend (Y : Finset ℕ) (l : ℕ) (f : ↥(Y.powersetCard l) → ℝ)
    (A : Finset ℕ) : ℝ := if h : A ∈ Y.powersetCard l then f ⟨A,h⟩ else 0

@[simp] theorem extend_coe (Y : Finset ℕ) (l : ℕ) (f : ↥(Y.powersetCard l) → ℝ)
    (A : ↥(Y.powersetCard l)) : extend Y l f A = f A := by simp [extend]

theorem K_extend (Y : Finset ℕ) (l : ℕ) (f : ↥(Y.powersetCard l) → ℝ) (A : Finset ℕ) :
    K Y l (extend Y l f) A = ∑ B : ↥(Y.powersetCard l), if Disjoint A B.val then f B else 0 := by
  classical
  rw [K, ← sum_coe_sort]
  apply sum_congr rfl
  intro B hB
  rw [extend_coe]

theorem K_one (Y A : Finset ℕ) (l : ℕ) (hA : A ∈ Y.powersetCard l) :
    K Y l (fun _ => 1) A = ((Y.card-l).choose l : ℝ) := by
  have hi : incidence ∅ = (fun _ : Finset ℕ => (1 : ℝ)) := by funext A; simp [incidence]
  rw [← hi]
  simpa using K_incidence Y A ∅ l hA (empty_subset Y) (by simp)

theorem K_quadratic_bound (Y : Finset ℕ) (l : ℕ) (hm : 2*l ≤ Y.card)
    (f : Finset ℕ → ℝ) (hf : ∑ A ∈ Y.powersetCard l, f A = 0) :
    |∑ A ∈ Y.powersetCard l, f A * K Y l f A| ≤
      ((Y.card-l-1).choose (l-1) : ℝ) * ∑ A ∈ Y.powersetCard l, f A ^ 2 := by
  classical
  let T := Y.powersetCard l
  let a : ↥T → ↥T → ℝ := fun A B => if Disjoint A.val B.val then 1 else 0
  have hs : ∀ A B, a A B = a B A := by
    intro A B
    simp only [a, disjoint_comm]
  have hd : ∀ A : ↥T, ∑ B : ↥T, a A B = ((Y.card-l).choose l : ℝ) := by
    intro A
    calc
      _ = ∑ B ∈ T, if Disjoint A.val B then (1 : ℝ) else 0 := sum_coe_sort T _
      _ = _ := K_one Y A.val l A.property
  have hb := symmetric_quadratic_bound a ((Y.card-l).choose l) ((Y.card-l-1).choose (l-1)) hs hd
    (by
      intro g μ hg hmean hne
      apply centered_eigenvalue_bound Y l (extend Y l g) μ hm
      · intro A hA
        rw [K_extend]
        simpa [a, extend, hA] using hg ⟨A,hA⟩
      · rw [← sum_coe_sort]
        simpa only [extend_coe] using hmean
      · by_contra hh
        apply hne
        funext A
        have hz : extend Y l g A.val = 0 := by
          by_contra hn
          exact hh ⟨A.val, A.property, hn⟩
        simpa using hz)
    (fun A : ↥T => f A.val) (by simpa only [sum_coe_sort] using hf)
  have hact (A : ↥T) : (∑ B : ↥T, a A B * f B.val) = K Y l f A.val := by
    simp only [a, ite_mul, one_mul, zero_mul]
    exact sum_coe_sort T (fun B : Finset ℕ => if Disjoint A.val B then f B else 0)
  simp only [hact] at hb
  have hq : (∑ A : ↥T, f A.val * K Y l f A.val) = ∑ A ∈ T, f A * K Y l f A := sum_coe_sort T (fun A : Finset ℕ => f A * K Y l f A)
  have hn : (∑ A : ↥T, f A.val ^ 2) = ∑ A ∈ T, f A ^ 2 := sum_coe_sort T (fun A : Finset ℕ => f A ^ 2)
  rw [hq, hn] at hb
  exact hb

end FranklKupavskii2022.EMC.Kneser

namespace FranklKupavskii2022.EMC.Kneser
open Finset
open FranklKupavskii2022.EMC.Exchange
set_option maxHeartbeats 1500000

noncomputable def chi (G : Finset (Finset ℕ)) (A : Finset ℕ) : ℝ := if A ∈ G then 1 else 0

theorem filter_family (T G : Finset (Finset ℕ)) (hG : G ⊆ T) : T.filter (fun A => A ∈ G) = G := by
  ext A
  simp only [mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hG h,h⟩⟩

theorem sum_chi (T G : Finset (Finset ℕ)) (hG : G ⊆ T) :
    ∑ A ∈ T, chi G A = (G.card : ℝ) := by
  classical
  simp only [chi, ← sum_filter, filter_family T G hG, sum_const, nsmul_eq_mul, mul_one]

theorem K_chi (Y A : Finset ℕ) (l : ℕ) (G : Finset (Finset ℕ))
    (hG : G ⊆ Y.powersetCard l) : K Y l (chi G) A = ∑ B ∈ G, if Disjoint A B then (1 : ℝ) else 0 := by
  classical
  unfold K
  calc
    _ = ∑ B ∈ Y.powersetCard l, if B ∈ G then (if Disjoint A B then (1 : ℝ) else 0) else 0 := by
      apply sum_congr rfl
      intro B hB
      by_cases h : B ∈ G <;> by_cases hd : Disjoint A B <;> simp [chi,h,hd]
    _ = _ := by rw [← sum_filter, filter_family _ G hG]

theorem pair_count_quadratic (Y : Finset ℕ) (l : ℕ) (G : Finset (Finset ℕ))
    (hG : G ⊆ Y.powersetCard l) :
    ∑ A ∈ Y.powersetCard l, chi G A * K Y l (chi G) A = ((disjointPairs G).card : ℝ) := by
  classical
  simp only [chi, ite_mul, one_mul, zero_mul, ← sum_filter, filter_family _ G hG]
  simp_rw [K_chi Y _ l G hG]
  simp only [disjointPairs, card_eq_sum_ones, sum_filter, sum_product, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem K_total (Y : Finset ℕ) (l : ℕ) (f : Finset ℕ → ℝ) :
    ∑ A ∈ Y.powersetCard l, K Y l f A = ((Y.card-l).choose l : ℝ) * ∑ A ∈ Y.powersetCard l, f A := by
  have h := K_symmetric Y l (fun _ => 1) f
  calc
    _ = ∑ A ∈ Y.powersetCard l, K Y l (fun _ => 1) A * f A := by simpa only [one_mul] using h
    _ = _ := by
      rw [mul_sum]
      exact sum_congr rfl (fun A hA => by rw [K_one Y A l hA])

theorem K_center (Y A : Finset ℕ) (l : ℕ) (f : Finset ℕ → ℝ) (α : ℝ)
    (hA : A ∈ Y.powersetCard l) :
    K Y l (fun B => f B - α) A = K Y l f A - α * ((Y.card-l).choose l : ℝ) := by
  have he : K Y l (fun B => f B - α) A = K Y l f A - α * K Y l (fun _ => 1) A := by
    classical
    simp only [K, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro B hB
    by_cases hd : Disjoint A B <;> simp [hd]
  rw [he, K_one Y A l hA]

theorem center_mean (T G : Finset (Finset ℕ)) (hG : G ⊆ T) (α : ℝ)
    (ha : (G.card : ℝ) = α * T.card) : ∑ A ∈ T, (chi G A - α) = 0 := by
  rw [sum_sub_distrib, sum_chi T G hG]
  simp only [sum_const, nsmul_eq_mul]
  rw [ha]; ring

theorem center_norm (T G : Finset (Finset ℕ)) (hG : G ⊆ T) (α : ℝ)
    (ha : (G.card : ℝ) = α * T.card) :
    ∑ A ∈ T, (chi G A - α)^2 = (T.card : ℝ)*α*(1-α) := by
  classical
  calc
    _ = ∑ A ∈ T, (chi G A * (1-2*α) + α^2) := by
      apply sum_congr rfl
      intro A hA
      by_cases h : A ∈ G <;> simp [chi,h] <;> ring
    _ = _ := by rw [sum_add_distrib, ← sum_mul, sum_chi T G hG]; simp only [sum_const,nsmul_eq_mul]; rw [ha]; ring

theorem center_quadratic (Y : Finset ℕ) (l : ℕ) (G : Finset (Finset ℕ))
    (hG : G ⊆ Y.powersetCard l) (α : ℝ)
    (ha : (G.card : ℝ) = α * (Y.powersetCard l).card) :
    ∑ A ∈ Y.powersetCard l, (chi G A - α) * K Y l (fun B => chi G B - α) A =
      ((disjointPairs G).card : ℝ) - ((Y.card-l).choose l : ℝ)*(Y.powersetCard l).card*α^2 := by
  classical
  calc
    _ = ∑ A ∈ Y.powersetCard l,
      (chi G A * K Y l (chi G) A - α * K Y l (chi G) A -
       (α * ((Y.card-l).choose l : ℝ)) * chi G A + α^2 * ((Y.card-l).choose l : ℝ)) := by
      apply sum_congr rfl
      intro A hA
      rw [K_center Y A l (chi G) α hA]
      ring
    _ = _ := by
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
      rw [pair_count_quadratic Y l G hG, K_total, sum_chi _ G hG, ha]
      ring

theorem kneser_mixing (Y : Finset ℕ) (l : ℕ) (hm : 2*l ≤ Y.card)
    (G : Finset (Finset ℕ)) (hG : G ⊆ Y.powersetCard l) (α : ℝ)
    (ha : (G.card : ℝ) = α * (Y.powersetCard l).card) :
    |((disjointPairs G).card : ℝ) - ((Y.card-l).choose l : ℝ)*(Y.powersetCard l).card*α^2| ≤
      ((Y.card-l-1).choose (l-1) : ℝ)*(Y.powersetCard l).card*α*(1-α) := by
  have hb := K_quadratic_bound Y l hm (fun A => chi G A - α) (center_mean _ G hG α ha)
  rw [center_norm _ G hG α ha, center_quadratic Y l G hG α ha] at hb
  convert hb using 1 <;> ring

end FranklKupavskii2022.EMC.Kneser

namespace FranklKupavskii2022.EMC.Kneser
open Finset
open FranklKupavskii2022.EMC.Exchange
set_option maxHeartbeats 1500000

theorem covariance_zero_size (m t : ℕ) (G : Finset (Finset ℕ))
    (hG : G ⊆ (Icc 1 m).powersetCard 0) (i j : Fin t) (hij : i ≠ j) :
    |cov m 0 t (etaI G i) (etaI G j)| ≤ density m 0 G * (1-density m 0 G)/((t:ℝ)-1) := by
  have hGs : G ⊆ {∅} := by simpa using hG
  have hc : G = ∅ ∨ G = {∅} := subset_singleton_iff.mp hGs
  rcases hc with rfl | rfl <;>
    rw [covariance_disjoint_pairs_choose m 0 t (by simp) _ hG i j hij] <;>
    norm_num [density, disjointPairs, Finset.filter_singleton]

theorem covariance_complete (m l t : ℕ) (hm : t*l ≤ m)
    (G : Finset (Finset ℕ)) (hG : G ⊆ (Icc 1 m).powersetCard l)
    (i j : Fin t) (hij : i ≠ j) :
    |cov m l t (etaI G i) (etaI G j)| ≤ density m l G*(1-density m l G)/((t:ℝ)-1) := by
  classical
  by_cases hl0 : l = 0
  · subst l; exact covariance_zero_size m t G hG i j hij
  have hl : 1 ≤ l := by omega
  have ht : 2 ≤ t := by
    by_contra hn
    have hv : i.val = j.val := by omega
    exact hij (Fin.ext hv)
  have h2l : 2*l ≤ m := (Nat.mul_le_mul_right l ht).trans hm
  have hml : l ≤ m := by omega
  have hml' : l ≤ m-l := by omega
  have hN : (0 : ℝ) < m.choose l := by exact_mod_cast Nat.choose_pos hml
  have hD : (0 : ℝ) < (m-l).choose l := by exact_mod_cast Nat.choose_pos hml'
  have htR : (0 : ℝ) < (t:ℝ)-1 := by
    have ht2 : (2:ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have hden : (0 : ℝ) < (m:ℝ)-(l:ℝ) := by
    have hlt : (l:ℝ) < m := by exact_mod_cast (show l < m by omega)
    linarith
  let α := density m l G
  have hY : (Icc 1 m).card = m := by simp [Nat.card_Icc]
  have hT : ((Icc 1 m).powersetCard l).card = m.choose l := by rw [card_powersetCard,hY]
  have ha : (G.card : ℝ) = α * ((Icc 1 m).powersetCard l).card := by
    rw [hT]
    dsimp [α,density]
    field_simp
  have hα0 : 0 ≤ α := by dsimp [α,density]; positivity
  have hα1 : α ≤ 1 := by
    dsimp [α,density]
    rw [div_le_one hN]
    exact_mod_cast (card_le_card hG).trans_eq hT
  have hv : 0 ≤ α*(1-α) := mul_nonneg hα0 (sub_nonneg.mpr hα1)
  have hb := kneser_mixing (Icc 1 m) l (by simpa only [hY] using h2l) G hG α ha
  rw [hY,hT] at hb
  have hcoef := coefficient_degree_identity m l hl h2l
  rw [Nat.cast_sub hml] at hcoef
  have hnrm : |((disjointPairs G).card:ℝ)/((m.choose l:ℝ)*((m-l).choose l:ℝ)) - α^2| ≤
      ((l:ℝ)/((m:ℝ)-(l:ℝ))) * (α*(1-α)) := by
    have he : ((disjointPairs G).card:ℝ)/((m.choose l:ℝ)*((m-l).choose l:ℝ)) - α^2 =
      (((disjointPairs G).card:ℝ) - ((m-l).choose l:ℝ)*(m.choose l:ℝ)*α^2)/
        ((m.choose l:ℝ)*((m-l).choose l:ℝ)) := by field_simp
    rw [he,abs_div,abs_of_pos (mul_pos hN hD),div_le_iff₀ (mul_pos hN hD)]
    have hc : ((m-l-1).choose (l-1):ℝ)*(m.choose l:ℝ)*α*(1-α) =
        ((l:ℝ)/((m:ℝ)-(l:ℝ))*(α*(1-α)))*((m.choose l:ℝ)*((m-l).choose l:ℝ)) := by
      apply (mul_left_cancel₀ hden.ne')
      field_simp
      nlinarith [congrArg (fun z:ℝ=>z*(m.choose l:ℝ)*α*(1-α)) hcoef]
    exact hb.trans_eq hc
  have hratio : (l:ℝ)/((m:ℝ)-(l:ℝ)) ≤ 1/((t:ℝ)-1) := by
    rw [div_le_div_iff₀ hden htR]
    have hmt : (t:ℝ)*(l:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    nlinarith
  rw [covariance_disjoint_pairs_choose m l t hm G hG i j hij]
  change |_ - α^2| ≤ α*(1-α)/((t:ℝ)-1)
  calc
    _ ≤ ((l:ℝ)/((m:ℝ)-(l:ℝ))) * (α*(1-α)) := hnrm
    _ ≤ (1/((t:ℝ)-1)) * (α*(1-α)) := mul_le_mul_of_nonneg_right hratio hv
    _ = _ := by ring

end FranklKupavskii2022.EMC.Kneser

open FranklKupavskii2022.EMC
theorem solution (m l t : ℕ) (hm : t * l ≤ m) (G : Finset (Finset ℕ))
    (hG : G ⊆ (Finset.Icc 1 m).powersetCard l) (i j : Fin t) (hij : i ≠ j) :
    |cov m l t (etaI G i) (etaI G j)| ≤
      density m l G * (1 - density m l G) / ((t : ℝ) - 1) :=
  Kneser.covariance_complete m l t hm G hG i j hij
