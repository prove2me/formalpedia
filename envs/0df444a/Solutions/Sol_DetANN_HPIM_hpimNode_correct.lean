-- Prove2me | solution 1 for DetANN.HPIM.hpimNode_correct
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T06:39:39.48839+00:00
-- url     : https://prove2.me/submissions/589b14b3-f48b-4442-8021-f09e4b165f73

import Mathlib
import Definitions.Def_DetANN_HPIMTree
import Theorems.Thm_DetANN_HPIM_lookupTree_spec
import Theorems.Thm_DetANN_HPIM_median_threshold
import Theorems.Thm_DetANN_HPIM_bisect_spec

/-!
# Correctness of the HPIM search, from the lookup contract, the median threshold and the ladder search
-/

namespace DetANN.HPIM

variable {m : ℕ}

section M4

open Classical

variable {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin m))

lemma thrReach_of_dist {d : ℝ} {i j : Fin n} (h : dist (P i) (P j) ≤ d) : thrReach P d i j := by
  by_cases hij : i = j
  · subst hij; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by rw [SimpleGraph.fromRel_adj]; exact ⟨hij, Or.inl h⟩)

lemma thrReach_symm {d : ℝ} {i j : Fin n} (h : thrReach P d i j) : thrReach P d j i :=
  SimpleGraph.Reachable.symm h

lemma thrReach_trans {d : ℝ} {i j k : Fin n} (h : thrReach P d i j) (h' : thrReach P d j k) :
    thrReach P d i k :=
  SimpleGraph.Reachable.trans h h'

lemma dist_le_of_thrReach {d : ℝ} (hd : 0 ≤ d) {i j : Fin n} (h : thrReach P d i j) :
    dist (P i) (P j) ≤ ((n : ℝ) - 1) * d :=
  (median_threshold P).1 d hd i j h

lemma medThreshold_spec (hn : 2 ≤ n) (hP : Function.Injective P) :
    (∃ i, n / 2 + 1 ≤ (Finset.univ.filter (thrReach P (medThreshold P) i)).card) ∧
    0 < medThreshold P ∧
    ∀ d' < medThreshold P, ∀ i, (Finset.univ.filter (thrReach P d' i)).card ≤ n / 2 :=
  (median_threshold P).2.2.2 hn hP

lemma exists_rep (d : ℝ) (i : Fin n) : ∃ j, thrReach P d i j ∧ IsRep P d j :=
  (median_threshold P).2.1 d i

lemma card_reps_le (d : ℝ) (i₀ : Fin n)
    (hbig : n / 2 + 1 ≤ (Finset.univ.filter (thrReach P d i₀)).card) :
    (Finset.univ.filter (IsRep P d)).card ≤ (n + 1) / 2 :=
  (median_threshold P).2.2.1 d i₀ hbig

end M4

section Node

open Classical

variable {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

lemma hpimNode_succ_eq (f : ℕ) (S : Finset (Fin N)) (h : ¬ S.card ≤ 1) :
    hpimNode Y δ (f + 1) S =
      .node S.card (MOf Y δ S) (Nat.clog 2 (MOf Y δ S - 1)) (ZOf Y δ S)
        (fun i => ((S.orderEmbOfFin rfl i : Fin N) : ℕ))
        (fun i => hpimNode Y δ f (compBotOf Y S i)) (hpimNode Y δ f (repsOf Y S)) := by
  rw [hpimNode, if_neg h]

lemma hpimNode_single (f : ℕ) (k : Fin N) :
    hpimNode Y δ f {k} = .single (k : ℕ) := by
  cases f with
  | zero => simp [hpimNode]
  | succ f => rw [hpimNode]; simp

end Node

lemma clog_child {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ (n + 1) / 2) :
    Nat.clog 2 k + 1 ≤ Nat.clog 2 n := by
  rw [Nat.clog_of_one_lt (n := n) (by norm_num) (by omega)]
  have : (n + 2 - 1) / 2 = (n + 1) / 2 := by omega
  rw [this]
  exact Nat.add_le_add_right (Nat.clog_mono_right 2 hk) 1

section NodeFacts

open Classical

variable {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

lemma ptsOf_injective (hY : Function.Injective Y) (S : Finset (Fin N)) :
    Function.Injective (ptsOf Y S) :=
  fun _ _ h => (S.orderEmbOfFin rfl).injective (hY h)

lemma rmedOf_pos (hY : Function.Injective Y) (S : Finset (Fin N)) (hS : 2 ≤ S.card) :
    0 < rmedOf Y S := by
  unfold rmedOf
  have := (medThreshold_spec (ptsOf Y S) hS (ptsOf_injective Y hY S)).2.1
  positivity

lemma lamOf_pos (hδ : 0 < δ) : 0 < lamOf N δ := by unfold lamOf; positivity

lemma rhoOf_pos (hY : Function.Injective Y) (hδ : 0 < δ) (S : Finset (Fin N)) (hS : 2 ≤ S.card)
    (k : ℕ) : 0 < rhoOf Y δ S k := by
  unfold rhoOf
  have := rmedOf_pos Y hY S hS
  positivity

lemma rhoOf_succ (S : Finset (Fin N)) (k : ℕ) :
    rhoOf Y δ S (k + 1) = (1 + δ / 4) * rhoOf Y δ S k := by
  unfold rhoOf; ring

lemma exists_ladder_top (hY : Function.Injective Y) (hδ : 0 < δ) (S : Finset (Fin N))
    (hS : 2 ≤ S.card) : ∃ k, bOf Y δ S ≤ rhoOf Y δ S k := by
  have hA : 0 < rmedOf Y S / 2 / 2 := by have := rmedOf_pos Y hY S hS; positivity
  have hc : 0 < 1 + δ / 4 := by positivity
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (bOf Y δ S * (1 + δ / 4) / (rmedOf Y S / 2 / 2))
    (by linarith : (1 : ℝ) < 1 + δ / 4)
  refine ⟨k, ?_⟩
  unfold rhoOf
  rw [le_div_iff₀ hc]
  rw [div_lt_iff₀ hA] at hk
  linarith

lemma MOf_eq (hY : Function.Injective Y) (hδ : 0 < δ) (S : Finset (Fin N)) (hS : 2 ≤ S.card) :
    MOf Y δ S = Nat.find (exists_ladder_top Y δ hY hδ S hS) + 1 := by
  unfold MOf; rw [dif_pos (exists_ladder_top Y δ hY hδ S hS)]

/-- The NearNbr contract of the `i`-th lookup of a node. -/
lemma lookup_node_spec (hm : 1 ≤ m) (hY : Function.Injective Y) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (S : Finset (Fin N)) (hS : 2 ≤ S.card) (i : ℕ) (hi : i < MOf Y δ S)
    (q : EuclideanSpace ℝ (Fin m)) :
    (∀ l, lookup (ZOf Y δ S) i q = some l →
      ∃ h : l < S.card, ‖q - ptsOf Y S ⟨l, h⟩‖ ≤ (1 + δ / 4) * rhoOf Y δ S i) ∧
    (lookup (ZOf Y δ S) i q = none → ∀ j, rhoOf Y δ S i < ‖q - ptsOf Y S j‖) := by
  have := (lookupTree_spec hm (n := S.card) (by omega) (ptsOf Y S) (rhoOf Y δ S i) δ
    (rhoOf_pos Y δ hY hδ S hS i) hδ hδ').1 q
  simp only [lookup, dif_pos hi]
  exact this

end NodeFacts

section M6

open Classical

variable {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

/-- The approximation factor after `L` levels. -/
lemma alphaOf_mono (hδ : 0 < δ) {L L' : ℕ} (h : L' ≤ L) : alphaOf N δ L' ≤ alphaOf N δ L := by
  unfold alphaOf
  have : 0 < 1 / lamOf N δ := by have := lamOf_pos (N := N) δ hδ; positivity
  gcongr
  · linarith

lemma one_le_alphaOf (hδ : 0 < δ) (L : ℕ) : 1 ≤ alphaOf N δ L := by
  unfold alphaOf
  have : 0 < 1 / lamOf N δ := by have := lamOf_pos (N := N) δ hδ; positivity
  have h1 : 1 ≤ (1 + 1 / lamOf N δ) ^ L := one_le_pow₀ (by linarith)
  have h2 : 1 ≤ (1 + δ / 4) ^ 2 := one_le_pow₀ (by linarith)
  nlinarith

lemma mem_of_orderEmb (S : Finset (Fin N)) (i : Fin S.card) : S.orderEmbOfFin rfl i ∈ S :=
  Finset.orderEmbOfFin_mem S rfl i

lemma exists_orderEmb_eq (S : Finset (Fin N)) {x : Fin N} (hx : x ∈ S) :
    ∃ j : Fin S.card, S.orderEmbOfFin rfl j = x := by
  have : x ∈ Set.range (S.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hx
  exact this

/-- **M6.** The HPIM search on a node with enough fuel returns a point of `S` that is an
`alphaOf N δ (⌈log₂ |S|⌉)`-approximate nearest neighbour of `q` in `S`. -/
theorem hpimNode_correct_aux (hm : 1 ≤ m) (hY : Function.Injective Y) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∀ f (S : Finset (Fin N)), S.Nonempty → Nat.clog 2 S.card < f →
      ∀ q : EuclideanSpace ℝ (Fin m), ∃ k ∈ S, (hpimNode Y δ f S).search q = (k : ℕ) ∧
        ∀ j ∈ S, ‖q - Y k‖ ≤ alphaOf N δ (Nat.clog 2 S.card) * ‖q - Y j‖ := by
  intro f
  induction f with
  | zero => intro S _ h; omega
  | succ f ih =>
    intro S hS hf q
    by_cases h1 : S.card ≤ 1
    · -- a single point
      have hc : S.card = 1 := le_antisymm h1 (Finset.card_pos.2 hS)
      obtain ⟨k, rfl⟩ := Finset.card_eq_one.1 hc
      refine ⟨k, Finset.mem_singleton_self _, by rw [hpimNode_single]; rfl, fun j hj => ?_⟩
      rw [Finset.mem_singleton.1 hj]
      have := one_le_alphaOf (N := N) δ hδ (Nat.clog 2 ({k} : Finset (Fin N)).card)
      nlinarith [norm_nonneg (q - Y k)]
    push Not at h1
    have hS2 : 2 ≤ S.card := h1
    set n := S.card with hn
    set e := S.orderEmbOfFin rfl with he
    set P := ptsOf Y S with hP
    have hPinj := ptsOf_injective Y hY S
    obtain ⟨⟨i₀, hbig⟩, hmedpos, hsmall⟩ := medThreshold_spec P hS2 hPinj
    have hrmed : rmedOf Y S = medThreshold P / 2 := rfl
    have hrpos : 0 < rmedOf Y S := rmedOf_pos Y hY S hS2
    have hlam := lamOf_pos (N := N) δ hδ
    set L := Nat.clog 2 n with hL
    have hLf : L ≤ f := by omega
    -- the nearest neighbour of q in S
    obtain ⟨xs, hxs, hmin⟩ := S.exists_min_image (fun j => ‖q - Y j‖) hS
    obtain ⟨js, rfl⟩ := exists_orderEmb_eq S hxs
    set D := ‖q - Y (e js)‖ with hD
    have hPe : ∀ a, P a = Y (e a) := fun _ => rfl
    have hfinal : ∀ k, ‖q - Y k‖ ≤ alphaOf N δ L * D →
        ∀ j ∈ S, ‖q - Y k‖ ≤ alphaOf N δ L * ‖q - Y j‖ := by
      intro k hk j hj
      exact hk.trans (mul_le_mul_of_nonneg_left (hmin j hj)
        (by have := one_le_alphaOf (N := N) δ hδ L; linarith))
    rw [hpimNode_succ_eq Y δ f S (by omega)]
    have hM := MOf_eq Y δ hY hδ S hS2
    have hM1 : 0 < MOf Y δ S := by omega
    rcases h0 : lookup (ZOf Y δ S) 0 q with _ | i
    · rcases hMl : lookup (ZOf Y δ S) (MOf Y δ S - 1) q with _ | l
      · ---------------------------------------------------------------- case (ii)
        simp only [HTree.search, h0, hMl]
        have hfar := (lookup_node_spec Y δ hm hY hδ hδ' S hS2 _ (by omega) q).2 hMl
        have htop : bOf Y δ S ≤ rhoOf Y δ S (MOf Y δ S - 1) := by
          rw [hM, Nat.add_sub_cancel]; exact Nat.find_spec (exists_ladder_top Y δ hY hδ S hS2)
        have hDb : bOf Y δ S < D := htop.trans_lt (hfar js)
        -- the representative of the nearest neighbour
        have h2r : 2 * rmedOf Y S = medThreshold P := by rw [hrmed]; ring
        obtain ⟨jr, hjr, hrep⟩ := exists_rep P (2 * rmedOf Y S) js
        have hrepmem : e jr ∈ repsOf Y S :=
          Finset.mem_map_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hrep⟩)
        have hdist : dist (P js) (P jr) ≤ ((n : ℝ) - 1) * (2 * rmedOf Y S) :=
          dist_le_of_thrReach P (by positivity) hjr
        have hcardR : (repsOf Y S).card ≤ (n + 1) / 2 := by
          unfold repsOf
          rw [Finset.card_map]
          have := card_reps_le P (2 * rmedOf Y S) i₀ (by rw [h2r]; exact hbig)
          convert this using 2
        have hRne : (repsOf Y S).Nonempty := ⟨_, hrepmem⟩
        have hcl := clog_child hS2 hcardR
        obtain ⟨k, hkR, hks, hkb⟩ := ih (repsOf Y S) hRne (by omega) q
        have hkS : k ∈ S := by
          obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hkR; exact mem_of_orderEmb S a
        refine ⟨k, hkS, hks, hfinal k ?_⟩
        have hb : bOf Y δ S = 2 * n * lamOf N δ * rmedOf Y S := rfl
        have hrep_le : ‖q - Y (e jr)‖ ≤ (1 + 1 / lamOf N δ) * D := by
          have h1 : ‖q - Y (e jr)‖ ≤ D + dist (P js) (P jr) := by
            rw [hD, ← hPe, ← hPe, dist_eq_norm]
            calc ‖q - P jr‖ = ‖(q - P js) + (P js - P jr)‖ := by congr 1; abel
              _ ≤ _ := norm_add_le _ _
          have h2 : ((n : ℝ) - 1) * (2 * rmedOf Y S) ≤ bOf Y δ S / lamOf N δ := by
            rw [hb, le_div_iff₀ hlam]
            have : (0 : ℝ) ≤ 2 * rmedOf Y S * lamOf N δ := by positivity
            nlinarith
          have h3 : bOf Y δ S / lamOf N δ ≤ D / lamOf N δ := by
            gcongr
          calc ‖q - Y (e jr)‖ ≤ D + D / lamOf N δ := by linarith
            _ = (1 + 1 / lamOf N δ) * D := by ring
        calc ‖q - Y k‖ ≤ alphaOf N δ (Nat.clog 2 (repsOf Y S).card) * ‖q - Y (e jr)‖ :=
              hkb _ hrepmem
          _ ≤ alphaOf N δ (L - 1) * ((1 + 1 / lamOf N δ) * D) := by
              gcongr
              · have := one_le_alphaOf (N := N) δ hδ (L - 1); linarith
              · exact alphaOf_mono δ hδ (by omega)
          _ = alphaOf N δ L * D := by
              unfold alphaOf
              have : L = (L - 1) + 1 := by omega
              conv_rhs => rw [this, pow_succ]
              ring
      · ---------------------------------------------------------------- case (iii)
        simp only [HTree.search, h0, hMl]
        have hstart0 : lookupC (ZOf Y δ S) 0 q = none := by
          simp only [lookupC, Nat.zero_min]; exact h0
        have hpow : MOf Y δ S - 1 ≤ 2 ^ Nat.clog 2 (MOf Y δ S - 1) := Nat.le_pow_clog (by norm_num) _
        have hstart1 : lookupC (ZOf Y δ S) (0 + 2 ^ Nat.clog 2 (MOf Y δ S - 1)) q ≠ none := by
          simp only [lookupC, zero_add, min_eq_right hpow, hMl]; simp
        obtain ⟨hlo, hhi, hge⟩ := (bisect_spec (ZOf Y δ S) q).1 _ 0 hstart0 hstart1
        set hi := bisect (ZOf Y δ S) q (Nat.clog 2 (MOf Y δ S - 1)) 0 with hhi_def
        have hhiM : hi ≤ MOf Y δ S - 1 := by
          by_contra hc
          push Not at hc
          have : lookupC (ZOf Y δ S) (hi - 1) q = lookup (ZOf Y δ S) (MOf Y δ S - 1) q := by
            simp only [lookupC, min_eq_right (by omega : MOf Y δ S - 1 ≤ hi - 1)]
          rw [this, hMl] at hlo
          exact absurd hlo (by simp)
        have hC1 : lookupC (ZOf Y δ S) hi q = lookup (ZOf Y δ S) hi q := by
          simp only [lookupC, min_eq_left hhiM]
        have hC0 : lookupC (ZOf Y δ S) (hi - 1) q = lookup (ZOf Y δ S) (hi - 1) q := by
          simp only [lookupC, min_eq_left (by omega : hi - 1 ≤ MOf Y δ S - 1)]
        rw [hC0] at hlo
        obtain ⟨i, hi_eq⟩ := Option.ne_none_iff_exists'.1 hhi
        rw [hi_eq]
        simp only
        rw [hC1] at hi_eq
        obtain ⟨hin, hqi⟩ := (lookup_node_spec Y δ hm hY hδ hδ' S hS2 hi (by omega) q).1 i hi_eq
        have hlow := (lookup_node_spec Y δ hm hY hδ hδ' S hS2 (hi - 1) (by omega) q).2 hlo js
        refine ⟨e ⟨i, hin⟩, mem_of_orderEmb S _, ?_, hfinal _ ?_⟩
        · simp [globOf, hin, e]
        · have hsucc : rhoOf Y δ S hi = (1 + δ / 4) * rhoOf Y δ S (hi - 1) := by
            have : hi = (hi - 1) + 1 := by omega
            conv_lhs => rw [this]
            exact rhoOf_succ Y δ S _
          have hα := alphaOf_mono (N := N) δ hδ (Nat.zero_le L)
          have hα0 : alphaOf N δ 0 = (1 + δ / 4) ^ 2 := by simp [alphaOf]
          rw [hα0] at hα
          calc ‖q - Y (e ⟨i, hin⟩)‖ = ‖q - P ⟨i, hin⟩‖ := rfl
            _ ≤ (1 + δ / 4) * rhoOf Y δ S hi := hqi
            _ = (1 + δ / 4) ^ 2 * rhoOf Y δ S (hi - 1) := by rw [hsucc]; ring
            _ ≤ (1 + δ / 4) ^ 2 * D := by gcongr; exact hlow.le
            _ ≤ alphaOf N δ L * D := by gcongr
    · ------------------------------------------------------------------ case (i)
      simp only [HTree.search, h0]
      obtain ⟨hin, hqi⟩ := (lookup_node_spec Y δ hm hY hδ hδ' S hS2 0 hM1 q).1 i h0
      rw [dif_pos hin]
      have hrho0 : (1 + δ / 4) * rhoOf Y δ S 0 = rmedOf Y S / 2 / 2 := by
        unfold rhoOf; field_simp
      have hreach : thrReach P (2 * (rmedOf Y S / 2)) ⟨i, hin⟩ js := by
        apply thrReach_of_dist
        rw [dist_eq_norm]
        have hle : D ≤ ‖q - P ⟨i, hin⟩‖ := hmin _ (mem_of_orderEmb S _)
        calc ‖P ⟨i, hin⟩ - P js‖ = ‖(q - P js) - (q - P ⟨i, hin⟩)‖ := by congr 1; abel
          _ ≤ ‖q - P js‖ + ‖q - P ⟨i, hin⟩‖ := norm_sub_le _ _
          _ ≤ 2 * (rmedOf Y S / 2 / 2) := by rw [← hPe] at hD; linarith
          _ ≤ 2 * (rmedOf Y S / 2) := by linarith
      have hmemC : e js ∈ compBotOf Y S ⟨i, hin⟩ :=
        Finset.mem_map_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hreach⟩)
      have hcardC : (compBotOf Y S ⟨i, hin⟩).card ≤ (n + 1) / 2 := by
        unfold compBotOf
        rw [Finset.card_map]
        have := hsmall (2 * (rmedOf Y S / 2)) (by rw [hrmed]; linarith) ⟨i, hin⟩
        refine le_trans (le_of_eq ?_) (this.trans (by omega))
        congr 1
      have hcl := clog_child hS2 hcardC
      obtain ⟨k, hkC, hks, hkb⟩ := ih (compBotOf Y S ⟨i, hin⟩) ⟨_, hmemC⟩ (by omega) q
      have hkS : k ∈ S := by
        obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hkC; exact mem_of_orderEmb S a
      refine ⟨k, hkS, hks, hfinal k ?_⟩
      calc ‖q - Y k‖ ≤ alphaOf N δ (Nat.clog 2 (compBotOf Y S ⟨i, hin⟩).card) * D := hkb _ hmemC
        _ ≤ alphaOf N δ L * D := by
            gcongr
            exact alphaOf_mono δ hδ (by omega)

end M6

end DetANN.HPIM

open DetANN.HPIM in
theorem solution {m N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (hm : 1 ≤ m)
    (hY : Function.Injective Y) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∀ f (S : Finset (Fin N)), S.Nonempty → Nat.clog 2 S.card < f →
      ∀ q : EuclideanSpace ℝ (Fin m), ∃ k ∈ S, (hpimNode Y δ f S).search q = (k : ℕ) ∧
        ∀ j ∈ S, ‖q - Y k‖ ≤ alphaOf N δ (Nat.clog 2 S.card) * ‖q - Y j‖ :=
  hpimNode_correct_aux Y δ hm hY hδ hδ'
