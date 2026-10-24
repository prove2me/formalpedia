-- Prove2me | solution 1 for ConstRegretMatch.Acyclic.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:04:07.21282+00:00
-- url     : https://prove2.me/submissions/3b0ef466-2258-4d2e-a62c-a800937cfec6

import Mathlib
import Definitions.Def_ConstRegretMatch_Acyclic_Network
import Definitions.Def_ConstRegretMatch_Acyclic_SPP
import Definitions.Def_ConstRegretMatch_Acyclic_Residual


namespace CRM51

open Matrix

/-- entries in {-1,0,1} -/
theorem mem3_mul {a b : ℝ} (ha : a = 0 ∨ a = 1 ∨ a = -1) (hb : b = 0 ∨ b = 1 ∨ b = -1) :
    a * b = 0 ∨ a * b = 1 ∨ a * b = -1 := by
  rcases ha with h | h | h <;> rcases hb with h' | h' | h' <;> subst h <;> subst h' <;> norm_num

theorem pow_neg_one_mem3 (k : ℕ) : ((-1 : ℝ) ^ k) = 0 ∨ ((-1 : ℝ) ^ k) = 1 ∨ ((-1 : ℝ) ^ k) = -1 := by
  rcases neg_one_pow_eq_or ℝ k with h | h <;> simp [h]

/-- Determinant of a `{-1,0,1}` square matrix with the "forest" peeling property lies in `{-1,0,1}`. -/
theorem det_mem3 : ∀ (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ),
    (∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1) →
    (∀ S T : Finset (Fin k), S.Nonempty →
      (∃ i ∈ S, (T.filter fun j => A i j ≠ 0).card ≤ 1) ∨
      (∃ j ∈ T, (S.filter fun i => A i j ≠ 0).card ≤ 1)) →
    A.det = 0 ∨ A.det = 1 ∨ A.det = -1 := by
  intro k
  induction k with
  | zero => intro A _ _; right; left; simp
  | succ k ih =>
    intro A hE hF
    -- inheritance to submatrices
    have hsub : ∀ (i j : Fin (k+1)),
        (A.submatrix i.succAbove j.succAbove).det = 0 ∨ (A.submatrix i.succAbove j.succAbove).det = 1 ∨
          (A.submatrix i.succAbove j.succAbove).det = -1 := by
      intro i j
      apply ih
      · intro a b; exact hE _ _
      · intro S T hS
        rcases hF (S.map i.succAboveEmb) (T.map j.succAboveEmb) (hS.map) with
          ⟨a, ha, hc⟩ | ⟨b, hb, hc⟩
        · left
          obtain ⟨a', ha', rfl⟩ := Finset.mem_map.1 ha
          refine ⟨a', ha', ?_⟩
          rw [Finset.filter_map, Finset.card_map] at hc
          convert hc using 2
          apply Finset.filter_congr
          intro x _
          simp [Fin.succAboveEmb]
        · right
          obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
          refine ⟨b', hb', ?_⟩
          rw [Finset.filter_map, Finset.card_map] at hc
          convert hc using 2
          apply Finset.filter_congr
          intro x _
          simp [Fin.succAboveEmb]
    rcases hF Finset.univ Finset.univ Finset.univ_nonempty with ⟨i, -, hc⟩ | ⟨j, -, hc⟩
    · rcases Finset.card_le_one_iff_subset_singleton.1 hc with ⟨j, hj⟩
      rw [det_succ_row A i, Finset.sum_eq_single j]
      · exact mem3_mul (mem3_mul (pow_neg_one_mem3 _) (hE i j)) (hsub i j)
      · intro b _ hb
        have : A i b = 0 := by
          by_contra hne
          have : b ∈ ({j} : Finset _) := hj (by simp [hne])
          exact hb (Finset.mem_singleton.1 this)
        simp [this]
      · simp
    · rcases Finset.card_le_one_iff_subset_singleton.1 hc with ⟨i, hi⟩
      rw [det_succ_column A j, Finset.sum_eq_single i]
      · exact mem3_mul (mem3_mul (pow_neg_one_mem3 _) (hE i j)) (hsub i j)
      · intro b _ hb
        have : A b j = 0 := by
          by_contra hne
          have : b ∈ ({i} : Finset _) := hi (by simp [hne])
          exact hb (Finset.mem_singleton.1 this)
        simp [this]
      · simp

/-- The inverse of an invertible matrix with the forest peeling property has entries in `{-1,0,1}`. -/
theorem inv_mem3 (k : ℕ) (A : Matrix (Fin k) (Fin k) ℝ)
    (hE : ∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1)
    (hF : ∀ S T : Finset (Fin k), S.Nonempty →
      (∃ i ∈ S, (T.filter fun j => A i j ≠ 0).card ≤ 1) ∨
      (∃ j ∈ T, (S.filter fun i => A i j ≠ 0).card ≤ 1))
    (hdet : A.det ≠ 0) :
    ∀ a b, A⁻¹ a b = 0 ∨ A⁻¹ a b = 1 ∨ A⁻¹ a b = -1 := by
  have hd : A.det = 1 ∨ A.det = -1 := by
    rcases det_mem3 k A hE hF with h | h | h
    · exact absurd h hdet
    · exact Or.inl h
    · exact Or.inr h
  intro a b
  have hadj : A.adjugate a b = 0 ∨ A.adjugate a b = 1 ∨ A.adjugate a b = -1 := by
    rw [adjugate_apply]
    apply det_mem3
    · intro i j
      by_cases hi : i = b
      · subst hi
        simp only [updateRow_self]
        by_cases hj : j = a
        · subst hj; simp
        · simp [hj]
      · rw [updateRow_ne hi]; exact hE i j
    · intro S T hS
      by_cases hb : b ∈ S
      · left
        refine ⟨b, hb, ?_⟩
        have key : ∀ j ∈ T.filter (fun j => A.updateRow b (Pi.single a 1) b j ≠ 0), j = a := by
          intro j hj
          simp only [Finset.mem_filter, updateRow_self] at hj
          by_contra hja
          simp [hja] at hj
        apply Finset.card_le_one.2
        intro x hx y hy
        rw [key x hx, key y hy]
      · rcases hF S T hS with ⟨i, hi, hc⟩ | ⟨j, hj, hc⟩
        · left
          refine ⟨i, hi, ?_⟩
          have hib : i ≠ b := fun h => hb (h ▸ hi)
          simpa [updateRow_ne hib] using hc
        · right
          refine ⟨j, hj, ?_⟩
          convert hc using 2
          apply Finset.filter_congr
          intro i hi
          have hib : i ≠ b := fun h => hb (h ▸ hi)
          simp [updateRow_ne hib]
  rw [inv_def, Matrix.smul_apply, smul_eq_mul]
  have hinv : Ring.inverse A.det = A.det := by
    rcases hd with h | h <;> rw [h] <;> simp
  rw [hinv]
  rcases hd with h | h <;> rw [h]
  · simpa using hadj
  · rcases hadj with h' | h' | h' <;> simp [h']

end CRM51


namespace CRM51

/-- In a finite nonempty acyclic graph some vertex has at most one neighbour. -/
theorem acyclic_exists_le_one {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) : ∃ u x, ∀ w, G.Adj u w → w = x := by
  classical
  obtain ⟨u, v, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  by_cases hnil : p.Nil
  · refine ⟨u, u, fun w hadj => ?_⟩
    exfalso
    have hlen := hmax u w hadj.toWalk hadj.isPath_toWalk
    rw [SimpleGraph.Walk.length_eq_zero_iff.2 hnil] at hlen
    simp at hlen
  · refine ⟨u, p.snd, fun w hadj => ?_⟩
    apply hG.eq_snd_of_adj_start hp hadj
    by_contra hw
    have hpc : (p.cons hadj.symm).IsPath := hp.cons hw
    have := hmax _ _ _ hpc
    simp at this

/-- Finset version: in an acyclic graph, every nonempty finite vertex set contains a vertex
with at most one neighbour inside the set. -/
theorem acyclic_finset_exists {V : Type} (G : SimpleGraph V) (hG : G.IsAcyclic)
    (W : Finset V) (hW : W.Nonempty) : ∃ u ∈ W, ∃ x, ∀ w ∈ W, G.Adj u w → w = x := by
  classical
  have : Nonempty (W : Set V) := ⟨⟨hW.choose, hW.choose_spec⟩⟩
  obtain ⟨u, x, hux⟩ := acyclic_exists_le_one (G.induce (W : Set V)) (hG.induce _)
  refine ⟨u.1, u.2, x.1, fun w hw hadj => ?_⟩
  have := hux ⟨w, hw⟩ (by simpa using hadj)
  rw [← this]

end CRM51


namespace CRM51

open ConstRegretMatch.Acyclic
open ConstRegretMatch.Upper (Mplus Qplus BasisIdx basicPart)
open Filter Topology

variable {n d : ℕ}

theorem mem_Mplus {z : Fin d → ℝ} {m : Fin d} : m ∈ Mplus z ↔ 0 < z m := by
  simp [ConstRegretMatch.Upper.Mplus]

theorem mem_Qplus {s : Fin n → ℝ} {j : Fin n} : j ∈ Qplus s ↔ 0 < s j := by
  simp [ConstRegretMatch.Upper.Qplus]

/-- No feasible direction at a unique optimum is weakly improving. -/
theorem no_dir (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ) (z : Fin d → ℝ)
    (s : Fin n → ℝ) (hU : SPPUniqueOptimal N r lam z s) (dz : Fin d → ℝ) (ds : Fin n → ℝ)
    (heq : ∀ i, ∑ m, N.M i m * dz m + ds i = 0)
    (hz : ∀ m, ¬ 0 < z m → 0 ≤ dz m) (hs : ∀ j, ¬ 0 < s j → 0 ≤ ds j)
    (hobj : 0 ≤ ∑ m, r m * dz m) : dz = 0 ∧ ds = 0 := by
  obtain ⟨⟨hz0, hs0, hfe⟩, hopt⟩ := hU.1
  have ev : ∀ (a b : ℝ), 0 ≤ a → (¬ 0 < a → 0 ≤ b) → ∀ᶠ t in 𝓝[>] (0:ℝ), 0 ≤ a + t * b := by
    intro a b ha hb
    by_cases hpos : 0 < a
    · have h1 : Tendsto (fun t : ℝ => a + t * b) (𝓝 0) (𝓝 (a + 0 * b)) :=
        tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds)
      rw [zero_mul, add_zero] at h1
      exact ((h1.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hpos)).mono
        fun t ht => ht.le
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : 0 < t := ht
      have := hb hpos
      have : 0 ≤ t * b := mul_nonneg ht'.le this
      linarith
  have hall : ∀ᶠ t in 𝓝[>] (0:ℝ), (∀ m, 0 ≤ z m + t * dz m) ∧ (∀ j, 0 ≤ s j + t * ds j) ∧ 0 < t := by
    refine (eventually_all.2 fun m => ev _ _ (hz0 m) (hz m)).and
      ((eventually_all.2 fun j => ev _ _ (hs0 j) (hs j)).and self_mem_nhdsWithin)
  obtain ⟨t, htz, hts, ht⟩ := hall.exists
  have hfeas : SPPFeasible N lam (fun m => z m + t * dz m) (fun j => s j + t * ds j) := by
    refine ⟨htz, hts, fun i => ?_⟩
    have h1 := hfe i
    have h2 := heq i
    simp only [mul_add, Finset.sum_add_distrib]
    have : ∑ m, N.M i m * (t * dz m) = t * ∑ m, N.M i m * dz m := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    rw [this]
    have h3 : t * (∑ m, N.M i m * dz m + ds i) = 0 := by rw [h2, mul_zero]
    linarith [h3]
  have hobj' : ∑ m, r m * (z m + t * dz m) = ∑ m, r m * z m + t * ∑ m, r m * dz m := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1; exact Finset.sum_congr rfl fun m _ => by ring
  have hopt' : SPPOptimal N r lam (fun m => z m + t * dz m) (fun j => s j + t * ds j) := by
    refine ⟨hfeas, fun z' s' hf' => ?_⟩
    have := hopt z' s' hf'
    rw [hobj']
    nlinarith [mul_nonneg ht.le hobj]
  obtain ⟨h1, h2⟩ := hU.2 _ _ hopt'
  constructor
  · funext m
    have := congrFun h1 m
    have : t * dz m = 0 := by linarith
    simpa [ht.ne'] using this
  · funext j
    have := congrFun h2 j
    have : t * ds j = 0 := by linarith
    simpa [ht.ne'] using this

/-- cost vector on the basis -/
noncomputable def rB (r : Fin d → ℝ) (z : Fin d → ℝ) (s : Fin n → ℝ) : BasisIdx z s → ℝ :=
  Sum.elim (fun m => r m.1) (fun _ => 0)

theorem solZ_inl {z : Fin d → ℝ} {s : Fin n → ℝ} (w : BasisIdx z s → ℝ) (m : {m // m ∈ Mplus z}) :
    basisSolZ w m.1 = w (Sum.inl m) := by
  simp [basisSolZ, m.2]

theorem lift_eq (N : MatchingNetwork n d) (z : Fin d → ℝ) (s : Fin n → ℝ)
    (w : BasisIdx z s → ℝ) (i : Fin n) :
    ∑ m, N.M i m * basisSolZ w m + basisSolS w i = ∑ c, basisMatrix N z s i c * w c := by
  classical
  rw [Fintype.sum_sum_type]
  congr 1
  · rw [← Finset.sum_subset (Finset.subset_univ (Mplus z)) (fun m _ hm => by
        simp [basisSolZ, hm]), ← Finset.sum_coe_sort]
    exact Finset.sum_congr rfl (fun m _ => by rw [solZ_inl]; simp [basisMatrix])
  · by_cases hi : i ∈ Qplus s
    · rw [Finset.sum_eq_single ⟨i, hi⟩]
      · simp [basisSolS, hi, basisMatrix]
      · intro j _ hj
        have : i ≠ j.1 := fun h => hj (Subtype.ext h.symm)
        simp [basisMatrix, this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [basisSolS, hi]
      · intro j _
        have : i ≠ j.1 := fun h => hi (h ▸ j.2)
        simp [basisMatrix, this]

theorem obj_eq (r : Fin d → ℝ) (z : Fin d → ℝ) (s : Fin n → ℝ) (w : BasisIdx z s → ℝ) :
    ∑ m, r m * basisSolZ w m = ∑ c, rB r z s c * w c := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [rB, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_subset (Finset.subset_univ (Mplus z)) (fun m _ hm => by
      simp [basisSolZ, hm]), ← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl (fun m _ => by rw [solZ_inl])

theorem solS_inr {z : Fin d → ℝ} {s : Fin n → ℝ} (w : BasisIdx z s → ℝ) (j : {j // j ∈ Qplus s}) :
    basisSolS w j.1 = w (Sum.inr j) := by
  simp [basisSolS, j.2]

theorem solZ_out {z : Fin d → ℝ} {s : Fin n → ℝ} (w : BasisIdx z s → ℝ) (m : Fin d)
    (hm : ¬ 0 < z m) : basisSolZ w m = 0 := by
  simp [basisSolZ, mem_Mplus, hm]

theorem solS_out {z : Fin d → ℝ} {s : Fin n → ℝ} (w : BasisIdx z s → ℝ) (j : Fin n)
    (hj : ¬ 0 < s j) : basisSolS w j = 0 := by
  simp [basisSolS, mem_Qplus, hj]

/-- kernel of the basis matrix in the weakly-improving direction is trivial -/
theorem kernel_trivial (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ) (z : Fin d → ℝ)
    (s : Fin n → ℝ) (hU : SPPUniqueOptimal N r lam z s) (w : BasisIdx z s → ℝ)
    (hw : ∀ i, ∑ c, basisMatrix N z s i c * w c = 0) (hobj : 0 ≤ ∑ c, rB r z s c * w c) :
    w = 0 := by
  obtain ⟨h1, h2⟩ := no_dir N r lam z s hU (basisSolZ w) (basisSolS w)
    (fun i => by rw [lift_eq]; exact hw i)
    (fun m hm => by rw [solZ_out w m hm])
    (fun j hj => by rw [solS_out w j hj])
    (by rw [obj_eq]; exact hobj)
  funext c
  rcases c with m | j
  · rw [← solZ_inl w m, h1]; rfl
  · rw [← solS_inr w j, h2]; rfl

end CRM51


namespace CRM51

open ConstRegretMatch.Acyclic
open ConstRegretMatch.Upper (Mplus Qplus BasisIdx basicPart)

variable {n d : ℕ}

theorem M_ne_zero (N : MatchingNetwork n d) (i : Fin n) (m : Fin d) : N.M i m ≠ 0 ↔ i ∈ N.A m := by
  unfold MatchingNetwork.M; split_ifs with h <;> simp [h]

theorem forest_prop (N : MatchingNetwork n d) (z : Fin d → ℝ) (s : Fin n → ℝ)
    (hac : (residualGraph N z).IsAcyclic) (e : BasisIdx z s ≃ Fin n) :
    ∀ S T : Finset (Fin n), S.Nonempty →
      (∃ i ∈ S, (T.filter fun k => basisMatrix N z s i (e.symm k) ≠ 0).card ≤ 1) ∨
      (∃ k ∈ T, (S.filter fun i => basisMatrix N z s i (e.symm k) ≠ 0).card ≤ 1) := by
  classical
  intro S T hS
  by_cases hslack : ∃ k ∈ T, ∃ j, e.symm k = Sum.inr j
  · right
    obtain ⟨k, hk, j, hj⟩ := hslack
    refine ⟨k, hk, Finset.card_le_one.2 ?_⟩
    intro a ha b hb
    simp only [Finset.mem_filter, hj, basisMatrix] at ha hb
    have ha' : a = j.1 := by by_contra h; simp [h] at ha
    have hb' : b = j.1 := by by_contra h; simp [h] at hb
    rw [ha', hb']
  · push_neg at hslack
    have hT : ∀ k ∈ T, ∃ m, e.symm k = Sum.inl m := by
      intro k hk
      cases h : e.symm k with
      | inl m => exact ⟨m, rfl⟩
      | inr j => exact absurd h (hslack k hk j)
    let W : Finset (Fin n ⊕ Fin d) := S.map Function.Embedding.inl ∪
      (Finset.univ.filter (fun m : {m // m ∈ Mplus z} => e (Sum.inl m) ∈ T)).image
        (fun m => Sum.inr m.1)
    have hW : W.Nonempty := by
      obtain ⟨i, hi⟩ := hS
      exact ⟨Sum.inl i, Finset.mem_union_left _ (Finset.mem_map_of_mem _ hi)⟩
    obtain ⟨u, hu, x, hx⟩ := acyclic_finset_exists _ hac W hW
    rcases Finset.mem_union.1 hu with hu | hu
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hu
      left
      refine ⟨i, hi, Finset.card_le_one.2 ?_⟩
      have key : ∀ a ∈ T.filter (fun k => basisMatrix N z s i (e.symm k) ≠ 0),
          ∃ m : {m // m ∈ Mplus z}, e.symm a = Sum.inl m ∧ Sum.inr m.1 = x := by
        intro a ha
        rw [Finset.mem_filter] at ha
        obtain ⟨m, hm⟩ := hT a ha.1
        refine ⟨m, hm, ?_⟩
        apply hx
        · apply Finset.mem_union_right
          apply Finset.mem_image.2
          refine ⟨m, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← hm, Equiv.apply_symm_apply]; exact ha.1
        · have h2 := ha.2
          rw [hm] at h2
          simp only [basisMatrix] at h2
          rw [M_ne_zero] at h2
          simp only [residualGraph, incidenceGraph]
          exact ⟨m.2, h2⟩
      intro a ha b hb
      obtain ⟨ma, hma, hxa⟩ := key a ha
      obtain ⟨mb, hmb, hxb⟩ := key b hb
      have : ma = mb := Subtype.ext (Sum.inr_injective (hxa.trans hxb.symm))
      apply e.symm.injective
      rw [hma, hmb, this]
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      right
      refine ⟨e (Sum.inl m), hm, Finset.card_le_one.2 ?_⟩
      have key : ∀ a ∈ S.filter (fun i => basisMatrix N z s i (e.symm (e (Sum.inl m))) ≠ 0),
          Sum.inl a = x := by
        intro a ha
        rw [Finset.mem_filter, Equiv.symm_apply_apply] at ha
        apply hx
        · exact Finset.mem_union_left _ (Finset.mem_map_of_mem _ ha.1)
        · have h2 := ha.2
          simp only [basisMatrix] at h2
          rw [M_ne_zero] at h2
          simp only [residualGraph, incidenceGraph]
          exact ⟨m.2, h2⟩
      intro a ha b hb
      exact Sum.inl_injective ((key a ha).trans (key b hb).symm)

end CRM51


namespace CRM51

open ConstRegretMatch.Acyclic
open ConstRegretMatch.Upper (Mplus Qplus BasisIdx basicPart)

variable {n d : ℕ}

theorem basis_entries (N : MatchingNetwork n d) (z : Fin d → ℝ) (s : Fin n → ℝ) (i : Fin n)
    (c : BasisIdx z s) :
    basisMatrix N z s i c = 0 ∨ basisMatrix N z s i c = 1 ∨ basisMatrix N z s i c = -1 := by
  rcases c with m | j
  · simp only [basisMatrix, MatchingNetwork.M]; split_ifs <;> simp
  · simp only [basisMatrix]; split_ifs <;> simp

/-- Main structural result: an inverse `Y` of the basis matrix with entries in `{-1,0,1}`. -/
theorem exists_inverse (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s)
    (hac : (residualGraph N z).IsAcyclic) :
    ∃ Y : BasisIdx z s → Fin n → ℝ,
      (∀ c i, Y c i = 0 ∨ Y c i = 1 ∨ Y c i = -1) ∧
      (∀ c c', ∑ i, Y c i * basisMatrix N z s i c' = if c = c' then 1 else 0) ∧
      (∀ i i', ∑ c, basisMatrix N z s i c * Y c i' = if i = i' then 1 else 0) := by
  classical
  have hcard : Fintype.card (BasisIdx z s) = Fintype.card (Fin n) := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin]
    exact hGP.2
  let e : BasisIdx z s ≃ Fin n := Fintype.equivOfCardEq hcard
  let B' : Matrix (Fin n) (Fin n) ℝ := fun i k => basisMatrix N z s i (e.symm k)
  have hdet : B'.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    let w : BasisIdx z s → ℝ := fun c => v (e c)
    have hBw : ∀ i, ∑ c, basisMatrix N z s i c * w c = 0 := by
      intro i
      have := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, B'] at this
      rw [← this, ← e.sum_comp]
      simp [w]
    have hw0 : w = 0 := by
      by_cases hsg : 0 ≤ ∑ c, rB r z s c * w c
      · exact kernel_trivial N r lam z s hGP.1 w hBw hsg
      · have := kernel_trivial N r lam z s hGP.1 (-w)
          (fun i => by simp [Finset.sum_neg_distrib, hBw i])
          (by simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]; linarith)
        exact neg_eq_zero.1 this
    apply hv0
    funext k
    have := congrFun hw0 (e.symm k)
    simpa [w] using this
  have hunit : IsUnit B'.det := isUnit_iff_ne_zero.2 hdet
  refine ⟨fun c i => B'⁻¹ (e c) i, ?_, ?_, ?_⟩
  · intro c i
    exact inv_mem3 n B' (fun i k => basis_entries N z s i _) (forest_prop N z s hac e) hdet _ _
  · intro c c'
    have h := congrFun (congrFun (Matrix.nonsing_inv_mul B' hunit) (e c)) (e c')
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simp only [B', Equiv.symm_apply_apply] at h
    rw [h]
    simp
  · intro i i'
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv B' hunit) i) i'
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h, ← e.sum_comp]
    simp [B']

end CRM51


open ConstRegretMatch.Acyclic CRM51
open ConstRegretMatch.Upper (Mplus Qplus BasisIdx basicPart)

theorem solution {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (hr : ConstRegretMatch.Upper.IsMatchValues r) (lam : Fin n → ℝ) (hlam : ConstRegretMatch.Upper.IsArrivalRates lam)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s)
    (hacyc : IsSPPAcyclic N r lam z s) :
    ∃ y : ConstRegretMatch.Upper.BasisIdx z s → Fin n → ℤ,
      (∀ c i, y c i = -1 ∨ y c i = 0 ∨ y c i = 1) ∧
      (∀ c, ConstRegretMatch.Upper.basicPart z s c = ∑ i, (y c i : ℝ) * lam i ∧ 0 < ∑ i, (y c i : ℝ) * lam i) ∧
      ∀ lamt : Fin n → ℝ, (∀ i, 0 < lamt i) → (∀ c, 0 < ∑ i, (y c i : ℝ) * lamt i) →
        SPPUniqueOptimal N r lamt
          (basisSolZ (fun c => ∑ i, (y c i : ℝ) * lamt i))
          (basisSolS (fun c => ∑ i, (y c i : ℝ) * lamt i)) := by
  classical
  obtain ⟨Y, hY3, hYB, hBY⟩ := exists_inverse N r lam z s hGP hacyc.2
  set B := basisMatrix N z s with hBdef
  let y : BasisIdx z s → Fin n → ℤ := fun c i =>
    if Y c i = 1 then 1 else if Y c i = -1 then -1 else 0
  have hy : ∀ c i, (y c i : ℝ) = Y c i := by
    intro c i
    rcases hY3 c i with h | h | h <;> norm_num [y, h]
  -- (a) B (Y x) = x
  have hA : ∀ (x : Fin n → ℝ) i, ∑ c, B i c * (∑ i', Y c i' * x i') = x i := by
    intro x i
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ i', ∑ c, B i c * (Y c i' * x i') = (∑ c, B i c * Y c i') * x i' := by
      intro i'; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
    simp_rw [this, hBY]
    simp
  -- (b) B w = x → w = Y x
  have hBinj : ∀ (w : BasisIdx z s → ℝ) (x : Fin n → ℝ), (∀ i, ∑ c, B i c * w c = x i) →
      ∀ c, w c = ∑ i, Y c i * x i := by
    intro w x hw c
    simp_rw [← hw, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ c', ∑ i, Y c i * (B i c' * w c') = (∑ i, Y c i * B i c') * w c' := by
      intro c'; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [this, hYB]
    simp
  obtain ⟨⟨hz0, hs0, hfe⟩, hopt⟩ := hGP.1.1
  have hzrec : basisSolZ (basicPart z s) = z := by
    funext m
    by_cases hm : 0 < z m
    · simp [basisSolZ, mem_Mplus, hm, basicPart]
    · rw [solZ_out _ m hm]; exact (le_antisymm (not_lt.1 hm) (hz0 m)).symm
  have hsrec : basisSolS (basicPart z s) = s := by
    funext j
    by_cases hj : 0 < s j
    · simp [basisSolS, mem_Qplus, hj, basicPart]
    · rw [solS_out _ j hj]; exact (le_antisymm (not_lt.1 hj) (hs0 j)).symm
  refine ⟨y, ?_, ?_, ?_⟩
  · intro c i
    rcases hY3 c i with h | h | h <;> norm_num [y, h]
  · intro c
    simp_rw [hy]
    have hb := hBinj (basicPart z s) lam (fun i => by
      rw [← lift_eq, hzrec, hsrec]; exact hfe i) c
    refine ⟨hb, ?_⟩
    rw [← hb]
    rcases c with m | j
    · exact mem_Mplus.1 m.2
    · exact mem_Qplus.1 j.2
  · intro lamt _ hpos
    simp_rw [hy] at hpos ⊢
    set wt : BasisIdx z s → ℝ := fun c => ∑ i, Y c i * lamt i with hwt
    -- dual vector
    let θ : Fin n → ℝ := fun i => ∑ c, rB r z s c * Y c i
    have hθB : ∀ c', ∑ i, B i c' * θ i = rB r z s c' := by
      intro c'
      simp only [θ, Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ c, ∑ i, B i c' * (rB r z s c * Y c i) = rB r z s c * ∑ i, Y c i * B i c' := by
        intro c; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      simp_rw [this, hYB]
      simp
    have hθM : ∀ m (hm : m ∈ Mplus z), ∑ i, N.M i m * θ i = r m := by
      intro m hm
      have := hθB (Sum.inl ⟨m, hm⟩)
      simpa [B, basisMatrix, rB] using this
    have hθQ : ∀ j (hj : j ∈ Qplus s), θ j = 0 := by
      intro j hj
      have := hθB (Sum.inr ⟨j, hj⟩)
      simpa [B, basisMatrix, rB] using this
    -- strict reduced costs off the basis
    have hθM' : ∀ m, ¬ 0 < z m → r m < ∑ i, N.M i m * θ i := by
      intro m hm
      by_contra hle
      push Not at hle
      let u : BasisIdx z s → ℝ := fun c => ∑ i, Y c i * N.M i m
      have hu := hA (fun i => N.M i m)
      obtain ⟨h1, -⟩ := no_dir N r lam z s hGP.1 ((Pi.single m (1:ℝ) : Fin d → ℝ) - basisSolZ u) (-basisSolS u)
        (fun i => by
          have h := lift_eq N z s u i
          have h2 := hu i
          simp only [Pi.sub_apply, Pi.neg_apply, mul_sub, Finset.sum_sub_distrib]
          have : ∑ m', N.M i m' * (Pi.single m (1:ℝ) : Fin d → ℝ) m' = N.M i m := by
            rw [Finset.sum_eq_single m]
            · simp
            · intro b _ hb; simp [Pi.single_apply, hb]
            · simp
          rw [this]
          linarith)
        (fun m' hm' => by
          rw [Pi.sub_apply, solZ_out u m' hm', sub_zero]
          by_cases h : m' = m
          · subst h; simp
          · simp [Pi.single_apply, h])
        (fun j hj => by rw [Pi.neg_apply, solS_out u j hj, neg_zero])
        (by
          simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
          rw [obj_eq]
          have : ∑ m', r m' * (Pi.single m (1:ℝ) : Fin d → ℝ) m' = r m := by
            rw [Finset.sum_eq_single m]
            · simp
            · intro b _ hb; simp [Pi.single_apply, hb]
            · simp
          rw [this]
          have : ∑ c, rB r z s c * u c = ∑ i, N.M i m * θ i := by
            simp only [u, θ, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => by ring
          rw [this]; linarith)
      have := congrFun h1 m
      simp [solZ_out u m hm] at this
    have hθQ' : ∀ j, ¬ 0 < s j → 0 < θ j := by
      intro j hj
      by_contra hle
      push Not at hle
      let u : BasisIdx z s → ℝ := fun c => Y c j
      obtain ⟨-, h2⟩ := no_dir N r lam z s hGP.1 (-basisSolZ u) ((Pi.single j (1:ℝ) : Fin n → ℝ) - basisSolS u)
        (fun i => by
          have h := lift_eq N z s u i
          have h2 := hBY i j
          simp only [Pi.sub_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
          have : (Pi.single j (1:ℝ) : Fin n → ℝ) i = if i = j then 1 else 0 := by
            by_cases hij : i = j
            · subst hij; simp
            · simp [Pi.single_apply, hij]
          rw [this, ← h2]
          simp only [u] at h
          linarith)
        (fun m hm => by rw [Pi.neg_apply, solZ_out u m hm, neg_zero])
        (fun j' hj' => by
          rw [Pi.sub_apply, solS_out u j' hj', sub_zero]
          by_cases h : j' = j
          · subst h; simp
          · simp [Pi.single_apply, h])
        (by
          simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
          rw [obj_eq]
          have : ∑ c, rB r z s c * u c = θ j := rfl
          rw [this]; linarith)
      have := congrFun h2 j
      simp [solS_out u j hj] at this
    -- weak duality identity
    have hid : ∀ (z' : Fin d → ℝ) (s' : Fin n → ℝ), (∀ i, ∑ m, N.M i m * z' m + s' i = lamt i) →
        ∑ i, θ i * lamt i = ∑ m, r m * z' m +
          (∑ m, (∑ i, N.M i m * θ i - r m) * z' m + ∑ j, θ j * s' j) := by
      intro z' s' h
      simp_rw [← h, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ m, ∑ i, θ i * (N.M i m * z' m) = (∑ i, N.M i m * θ i) * z' m := by
        intro m; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
      simp_rw [this, sub_mul, Finset.sum_sub_distrib]
      ring
    have hgap_nonneg : ∀ (z' : Fin d → ℝ) (s' : Fin n → ℝ), (∀ m, 0 ≤ z' m) → (∀ j, 0 ≤ s' j) →
        (∀ m, 0 ≤ (∑ i, N.M i m * θ i - r m) * z' m) ∧ (∀ j, 0 ≤ θ j * s' j) := by
      intro z' s' hz' hs'
      constructor
      · intro m
        by_cases hm : 0 < z m
        · rw [hθM m (mem_Mplus.2 hm)]; simp
        · exact mul_nonneg (by linarith [hθM' m hm]) (hz' m)
      · intro j
        by_cases hj : 0 < s j
        · rw [hθQ j (mem_Qplus.2 hj)]; simp
        · exact mul_nonneg (hθQ' j hj).le (hs' j)
    -- feasibility of the candidate
    have hfeas : SPPFeasible N lamt (basisSolZ wt) (basisSolS wt) := by
      refine ⟨fun m => ?_, fun j => ?_, fun i => ?_⟩
      · by_cases hm : 0 < z m
        · rw [solZ_inl wt ⟨m, mem_Mplus.2 hm⟩]; exact (hpos _).le
        · rw [solZ_out wt m hm]
      · by_cases hj : 0 < s j
        · rw [solS_inr wt ⟨j, mem_Qplus.2 hj⟩]; exact (hpos _).le
        · rw [solS_out wt j hj]
      · rw [lift_eq]; exact hA lamt i
    -- candidate has zero gap
    have hcand : ∑ i, θ i * lamt i = ∑ m, r m * basisSolZ wt m := by
      rw [hid _ _ hfeas.2.2]
      have h1 : ∀ m, (∑ i, N.M i m * θ i - r m) * basisSolZ wt m = 0 := by
        intro m
        by_cases hm : 0 < z m
        · rw [hθM m (mem_Mplus.2 hm)]; simp
        · rw [solZ_out wt m hm]; simp
      have h2 : ∀ j, θ j * basisSolS wt j = 0 := by
        intro j
        by_cases hj : 0 < s j
        · rw [hθQ j (mem_Qplus.2 hj)]; simp
        · rw [solS_out wt j hj]; simp
      simp [h1, h2]
    have hoptc : SPPOptimal N r lamt (basisSolZ wt) (basisSolS wt) := by
      refine ⟨hfeas, fun z' s' hf => ?_⟩
      rw [← hcand, hid z' s' hf.2.2]
      obtain ⟨g1, g2⟩ := hgap_nonneg z' s' hf.1 hf.2.1
      have := Finset.sum_nonneg fun m (_ : m ∈ Finset.univ) => g1 m
      have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => g2 j
      linarith
    refine ⟨hoptc, fun z' s' ho => ?_⟩
    have hf := ho.1
    have hge := ho.2 _ _ hfeas
    have hle := hoptc.2 _ _ hf
    obtain ⟨g1, g2⟩ := hgap_nonneg z' s' hf.1 hf.2.1
    have hsum := hid z' s' hf.2.2
    rw [hcand] at hsum
    have hs1 := Finset.sum_nonneg fun m (_ : m ∈ Finset.univ) => g1 m
    have hs2 := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => g2 j
    have e1 : ∑ m, (∑ i, N.M i m * θ i - r m) * z' m = 0 := by linarith
    have e2 : ∑ j, θ j * s' j = 0 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg fun m _ => g1 m] at e1
    rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => g2 j] at e2
    have hz'0 : ∀ m, ¬ 0 < z m → z' m = 0 := by
      intro m hm
      have := e1 m (Finset.mem_univ _)
      rcases mul_eq_zero.1 this with h | h
      · linarith [hθM' m hm]
      · exact h
    have hs'0 : ∀ j, ¬ 0 < s j → s' j = 0 := by
      intro j hj
      have := e2 j (Finset.mem_univ _)
      rcases mul_eq_zero.1 this with h | h
      · linarith [hθQ' j hj]
      · exact h
    let w' : BasisIdx z s → ℝ := Sum.elim (fun m => z' m.1) (fun j => s' j.1)
    have hzw : basisSolZ w' = z' := by
      funext m
      by_cases hm : 0 < z m
      · rw [solZ_inl w' ⟨m, mem_Mplus.2 hm⟩]; rfl
      · rw [solZ_out w' m hm, hz'0 m hm]
    have hsw : basisSolS w' = s' := by
      funext j
      by_cases hj : 0 < s j
      · rw [solS_inr w' ⟨j, mem_Qplus.2 hj⟩]; rfl
      · rw [solS_out w' j hj, hs'0 j hj]
    have hw'eq : w' = wt := by
      funext c
      exact hBinj w' lamt (fun i => by rw [← lift_eq, hzw, hsw]; exact hf.2.2 i) c
    rw [← hzw, ← hsw, hw'eq]
    exact ⟨rfl, rfl⟩
