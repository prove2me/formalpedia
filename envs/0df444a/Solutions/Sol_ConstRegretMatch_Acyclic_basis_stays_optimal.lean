-- Prove2me | solution 1 for ConstRegretMatch.Acyclic.basis_stays_optimal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:09:15.885985+00:00
-- url     : https://prove2.me/submissions/f9252a1c-773a-4cb2-8b1b-dcfd1dc2b165

import Mathlib
import Definitions.Def_ConstRegretMatch_Acyclic_Network
import Definitions.Def_ConstRegretMatch_Acyclic_SPP

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

/-- Under GP the basis matrix has a two-sided inverse. -/
theorem exists_inv_gen (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s)
 :
    ∃ Y : BasisIdx z s → Fin n → ℝ,
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
  refine ⟨fun c i => B'⁻¹ (e c) i, ?_, ?_⟩
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



theorem opt_of_pos (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hU : SPPUniqueOptimal N r lam z s)
    (Y : BasisIdx z s → Fin n → ℝ)
    (hYB : ∀ c c', ∑ i, Y c i * basisMatrix N z s i c' = if c = c' then 1 else 0)
    (hBY : ∀ i i', ∑ c, basisMatrix N z s i c * Y c i' = if i = i' then 1 else 0)
    (lamt : Fin n → ℝ) (hpos : ∀ c, 0 < ∑ i, Y c i * lamt i) :
    SPPUniqueOptimal N r lamt (basisSolZ (fun c => ∑ i, Y c i * lamt i))
      (basisSolS (fun c => ∑ i, Y c i * lamt i)) := by
  classical
  set B := basisMatrix N z s with hBdef
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
    obtain ⟨h1, -⟩ := no_dir N r lam z s hU ((Pi.single m (1:ℝ) : Fin d → ℝ) - basisSolZ u) (-basisSolS u)
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
    obtain ⟨-, h2⟩ := no_dir N r lam z s hU (-basisSolZ u) ((Pi.single j (1:ℝ) : Fin n → ℝ) - basisSolS u)
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


end CRM51


namespace CRM51

open ConstRegretMatch.Acyclic
open ConstRegretMatch.Upper (Mplus Qplus BasisIdx basicPart)

variable {n d : ℕ}

theorem basic_eq (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hU : SPPUniqueOptimal N r lam z s)
    (Y : BasisIdx z s → Fin n → ℝ)
    (hYB : ∀ c c', ∑ i, Y c i * basisMatrix N z s i c' = if c = c' then 1 else 0) :
    ∀ c, basicPart z s c = ∑ i, Y c i * lam i ∧ 0 < ∑ i, Y c i * lam i := by
  classical
  set B := basisMatrix N z s with hBdef
  have hBinj : ∀ (w : BasisIdx z s → ℝ) (x : Fin n → ℝ), (∀ i, ∑ c, B i c * w c = x i) →
      ∀ c, w c = ∑ i, Y c i * x i := by
    intro w x hw c
    simp_rw [← hw, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ c', ∑ i, Y c i * (B i c' * w c') = (∑ i, Y c i * B i c') * w c' := by
      intro c'; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [this, hYB]
    simp
  obtain ⟨⟨hz0, hs0, hfe⟩, hopt⟩ := hU.1
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
  intro c
  have hb := hBinj (basicPart z s) lam (fun i => by
    rw [← lift_eq, hzrec, hsrec]; exact hfe i) c
  refine ⟨hb, ?_⟩
  rw [← hb]
  rcases c with m | j
  · exact mem_Mplus.1 m.2
  · exact mem_Qplus.1 j.2

end CRM51


open ConstRegretMatch.Acyclic CRM51
open Filter Topology

theorem solution {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (hr : ConstRegretMatch.Upper.IsMatchValues r) (lam : Fin n → ℝ) (hlam : ConstRegretMatch.Upper.IsArrivalRates lam)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s) :
    ∃ ζ₀ : ℝ, 0 < ζ₀ ∧
      ∀ lamt : Fin n → ℝ, (∀ i, 0 < lamt i) → (∀ i, |lamt i - lam i| ≤ ζ₀) →
        ∃ w : ConstRegretMatch.Upper.BasisIdx z s → ℝ, SPPOptimal N r lamt (basisSolZ w) (basisSolS w) := by
  classical
  obtain ⟨Y, hYB, hBY⟩ := exists_inv_gen N r lam z s hGP
  have hbp := fun c => (basic_eq N r lam z s hGP.1 Y hYB c).2
  have ev : ∀ᶠ ζ in 𝓝[>] (0:ℝ), ∀ c, 0 < ∑ i, Y c i * lam i - (∑ i, |Y c i|) * ζ := by
    refine eventually_all.2 fun c => ?_
    have h1 : Tendsto (fun ζ : ℝ => ∑ i, Y c i * lam i - (∑ i, |Y c i|) * ζ) (𝓝 0)
        (𝓝 (∑ i, Y c i * lam i - (∑ i, |Y c i|) * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_id)
    rw [mul_zero, sub_zero] at h1
    exact (h1.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds (hbp c))
  obtain ⟨ζ, hζ, hζ0⟩ := (ev.and self_mem_nhdsWithin).exists
  refine ⟨ζ, hζ0, fun lamt _ hclose => ⟨_, (opt_of_pos N r lam z s hGP.1 Y hYB hBY lamt ?_).1⟩⟩
  intro c
  have hi : ∀ i, Y c i * lam i - |Y c i| * ζ ≤ Y c i * lamt i := by
    intro i
    have h1 : |Y c i * (lamt i - lam i)| ≤ |Y c i| * ζ := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hclose i) (abs_nonneg _)
    have h2 := neg_abs_le (Y c i * (lamt i - lam i))
    have h3 : Y c i * (lamt i - lam i) = Y c i * lamt i - Y c i * lam i := by ring
    linarith
  have hsum : ∑ i, Y c i * lam i - (∑ i, |Y c i|) * ζ ≤ ∑ i, Y c i * lamt i := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => hi i
  linarith [hζ c]
