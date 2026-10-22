-- Prove2me | solution 1 for BirkhoffGlobalSection.closed_preconnected_locally_convex_is_convex
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T22:56:22.663678+00:00
-- url     : https://prove2.me/submissions/b25da501-bf64-4c2c-bdd3-ab20e00dff61

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.ProperSpace

open scoped Topology
open Set Metric Filter
namespace BirkhoffGlobalSection

theorem locallyConvexSet_locallyPathConnected (K : Set Phase)
    (hloc : ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U)) :
    LocallyPathConnectedSpace K := by
  refine ⟨fun x ↦ ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨t, ht⟩ ↦ mem_of_superset ht.1.1 ht.2⟩⟩⟩
  obtain ⟨t, ht⟩ := (mem_nhds_subtype K x s).mp hs
  obtain ⟨U, hU, hc⟩ := hloc x x.property
  obtain ⟨V, hV, hsub⟩ :=
    (LocallyConvexSpace.convex_basis (𝕜 := ℝ) x.1).mem_iff.mp (inter_mem ht.1 hU)
  refine ⟨(↑) ⁻¹' V, ⟨?_, ?_⟩, (preimage_mono (hsub.trans inter_subset_left)).trans ht.2⟩
  · exact continuousAt_subtype_val.preimage_mem_nhds hV.1
  · refine Subtype.preimage_coe_self_inter _ _ ▸ IsPathConnected.preimage_coe ?_ inter_subset_left
    have heq : K ∩ V = (K ∩ U) ∩ V := by
      ext y
      constructor
      · rintro ⟨hy, hv⟩
        exact ⟨⟨hy, (hsub hv).2⟩, hv⟩
      · rintro ⟨⟨hy, _⟩, hv⟩
        exact ⟨hy, hv⟩
    rw [heq]
    exact (hc.inter hV.2).isPathConnected ⟨x, ⟨x.property, mem_of_mem_nhds hU⟩,
      mem_of_mem_nhds hV.1⟩

theorem locallyConvexSet_uniform_radius (K A : Set Phase) (hA : IsCompact A)
    (hAK : A ⊆ K)
    (hloc : ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U)) :
    ∃ δ > 0, ∀ x ∈ A, Convex ℝ (K ∩ ball x δ) := by
  have hballs : ∀ x : K, ∃ r > 0, Convex ℝ (K ∩ ball (x : Phase) r) := by
    intro x
    obtain ⟨U, hU, hc⟩ := hloc x x.property
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
    refine ⟨r, hr, ?_⟩
    have heq : K ∩ ball (x : Phase) r = (K ∩ U) ∩ ball (x : Phase) r := by
      ext y
      simp only [mem_inter_iff]
      exact ⟨fun h => ⟨⟨h.1, hrU h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [heq]
    exact hc.inter (convex_ball _ _)
  choose r hr hc using hballs
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric
    (c := fun x : K => ball (x : Phase) (r x)) hA
    (fun x : K => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hAK hx⟩, mem_ball_self (hr _)⟩)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  obtain ⟨z, hz⟩ := hcover x hx
  have heq : K ∩ ball x δ = (K ∩ ball (z : Phase) (r z)) ∩ ball x δ := by
    ext y
    simp only [mem_inter_iff]
    exact ⟨fun h => ⟨⟨h.1, hz h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  rw [heq]
  exact (hc z).inter (convex_ball _ _)

theorem locallyConvexSet_isPathConnected (K : Set Phase)
    (hconn : IsPreconnected K) (hne : K.Nonempty)
    (hloc : ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U)) :
    IsPathConnected K := by
  let : ConnectedSpace K := isConnected_iff_connectedSpace.mp ⟨hne, hconn⟩
  let : LocallyPathConnectedSpace K := locallyConvexSet_locallyPathConnected K hloc
  let : PathConnectedSpace K := PathConnectedSpace.of_locallyPathConnectedSpace
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

def chainEdgeEnergy (a b : Phase) : ℝ := ∑ i : Fin 4, (b i - a i) ^ 2

theorem chain_midpoint_energy_identity (a b c : Phase) :
    chainEdgeEnergy a b + chainEdgeEnergy b c -
      (chainEdgeEnergy a ((1 / 2 : ℝ) • (a + c)) +
        chainEdgeEnergy ((1 / 2 : ℝ) • (a + c)) c) =
    2 * chainEdgeEnergy ((1 / 2 : ℝ) • (a + c)) b := by
  simp only [chainEdgeEnergy, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem chain_midpoint_of_minimal_energy (a b c : Phase)
    (h : chainEdgeEnergy a b + chainEdgeEnergy b c ≤
      chainEdgeEnergy a ((1 / 2 : ℝ) • (a + c)) +
        chainEdgeEnergy ((1 / 2 : ℝ) • (a + c)) c) :
    b = (1 / 2 : ℝ) • (a + c) := by
  have hn : 0 ≤ chainEdgeEnergy ((1 / 2 : ℝ) • (a + c)) b :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hz : chainEdgeEnergy ((1 / 2 : ℝ) • (a + c)) b = 0 := by
    have hi := chain_midpoint_energy_identity a b c
    linarith
  have he := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
      sq_nonneg (b i - ((1 / 2 : ℝ) • (a + c)) i))).mp hz
  ext i
  have hi := he i (Finset.mem_univ i)
  nlinarith [sq_nonneg (b i - ((1 / 2 : ℝ) • (a + c)) i)]

open scoped unitInterval

theorem continuous_path_small_chain (C : Set Phase) (γ : I → Phase)
    (hγ : Continuous γ) (hC : ∀ t, γ t ∈ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ p : Fin (N + 1) → Phase,
      p 0 = γ 0 ∧ p (Fin.last N) = γ 1 ∧
      (∀ i, p i ∈ C) ∧ (∀ i : Fin N, dist (p i.castSucc) (p i.succ) < ε) := by
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, htcover⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun u : I => γ ⁻¹' ball (γ u) (ε / 2))
      (fun u => isOpen_ball.preimage hγ) (by
        intro u _
        exact mem_iUnion.mpr ⟨u, mem_ball_self (by linarith)⟩)
  let N := m + 1
  let p : Fin (N + 1) → Phase := fun i => γ (t i.val)
  refine ⟨N, by omega, p, ?_, ?_, fun i => hC _, ?_⟩
  · change γ (t 0) = γ 0
    rw [ht0]
  · change γ (t N) = γ 1
    rw [hm N (by dsimp [N]; omega)]
  · intro i
    obtain ⟨u, hu⟩ := htcover i.val
    have hleft := hu (left_mem_Icc.mpr (htmono (Nat.le_succ i.val)))
    have hright := hu (right_mem_Icc.mpr (htmono (Nat.le_succ i.val)))
    have hl : dist (γ (t i.val)) (γ u) < ε / 2 := hleft
    have hr : dist (γ (t (i.val + 1))) (γ u) < ε / 2 := hright
    change dist (γ (t i.val)) (γ (t (i.val + 1))) < ε
    have htri := dist_triangle (γ (t i.val)) (γ u) (γ (t (i.val + 1)))
    rw [dist_comm (γ u)] at htri
    linarith

def admissibleChain (C : Set Phase) (N : ℕ) (x y : Phase) (ε : ℝ) :
    Set (Fin (N + 1) → Phase) :=
  {p | (∀ i, p i ∈ C) ∧ p 0 = x ∧ p (Fin.last N) = y ∧
    ∀ i : Fin N, dist (p i.castSucc) (p i.succ) ≤ ε}

def chainEnergy (N : ℕ) (p : Fin (N + 1) → Phase) : ℝ :=
  ∑ i : Fin N, chainEdgeEnergy (p i.castSucc) (p i.succ)

theorem admissibleChain_isCompact (C : Set Phase) (hC : IsCompact C)
    (N : ℕ) (x y : Phase) (ε : ℝ) : IsCompact (admissibleChain C N x y ε) := by
  have hl : IsClosed {p : Fin (N + 1) → Phase | p 0 = x} :=
    isClosed_eq (continuous_apply 0) continuous_const
  have hr : IsClosed {p : Fin (N + 1) → Phase | p (Fin.last N) = y} :=
    isClosed_eq (continuous_apply _) continuous_const
  have he : IsClosed {p : Fin (N + 1) → Phase |
      ∀ i : Fin N, dist (p i.castSucc) (p i.succ) ≤ ε} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i =>
      isClosed_le ((continuous_apply i.castSucc).dist (continuous_apply i.succ)) continuous_const
  simpa only [admissibleChain, ofPred_and] using
    (isCompact_pi_infinite (fun _ : Fin (N + 1) => hC)).inter_right (hl.inter (hr.inter he))

theorem chainEnergy_continuous (N : ℕ) : Continuous (chainEnergy N) := by
  unfold chainEnergy chainEdgeEnergy
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  have hl : Continuous (fun p : Fin (N + 1) → Phase => p i.castSucc j) :=
    (continuous_apply j).comp (continuous_apply i.castSucc)
  have hr : Continuous (fun p : Fin (N + 1) → Phase => p i.succ j) :=
    (continuous_apply j).comp (continuous_apply i.succ)
  exact (hr.sub hl).pow 2

theorem admissibleChain_exists_energy_minimizer (C : Set Phase) (hC : IsCompact C)
    (N : ℕ) (x y : Phase) (ε : ℝ) (hne : (admissibleChain C N x y ε).Nonempty) :
    ∃ p ∈ admissibleChain C N x y ε,
      ∀ q ∈ admissibleChain C N x y ε, chainEnergy N p ≤ chainEnergy N q := by
  exact (admissibleChain_isCompact C hC N x y ε).exists_isMinOn hne
    (chainEnergy_continuous N).continuousOn

theorem local_chain_midpoint_admissible (K B : Set Phase) (hB : Convex ℝ B)
    (a b c : Phase) (ha : a ∈ K ∩ B) (hc : c ∈ K ∩ B)
    (δ ε : ℝ) (hεδ : ε < δ)
    (hlab : dist a b ≤ ε) (hrbc : dist b c ≤ ε)
    (hloc : Convex ℝ (K ∩ ball b δ)) :
    (1 / 2 : ℝ) • (a + c) ∈ K ∩ B ∧
      dist a ((1 / 2 : ℝ) • (a + c)) ≤ ε ∧
      dist ((1 / 2 : ℝ) • (a + c)) c ≤ ε := by
  have ha' : a ∈ K ∩ ball b δ := ⟨ha.1, hlab.trans_lt hεδ⟩
  have hc' : c ∈ K ∩ ball b δ := ⟨hc.1, by
    rw [mem_ball, dist_comm]
    exact hrbc.trans_lt hεδ⟩
  have hmK := (hloc.midpoint_mem ha' hc').1
  have hmB := hB.midpoint_mem ha.2 hc.2
  have htri := dist_triangle a b c
  have hl : dist a (midpoint ℝ a c) = (1 / 2 : ℝ) * dist a c := by
    norm_num [dist_left_midpoint]
  have hr : dist (midpoint ℝ a c) c = (1 / 2 : ℝ) * dist a c := by
    norm_num [dist_midpoint_right]
  have hmid : midpoint ℝ a c = (1 / 2 : ℝ) • (a + c) := by
    simp [midpoint_eq_smul_add]
  rw [hmid] at hmK hmB hl hr
  refine ⟨⟨hmK, hmB⟩, ?_, ?_⟩ <;> linarith

theorem two_term_sum_comparison {ι : Type*} [Fintype ι]
    (f g : ι → ℝ) (u v : ι) (huv : u ≠ v)
    (hsame : ∀ i, i ≠ u → i ≠ v → f i = g i)
    (hle : (∑ i, f i) ≤ ∑ i, g i) : f u + f v ≤ g u + g v := by
  classical
  have hv : v ∈ (Finset.univ : Finset ι).erase u := by
    simp [huv.symm]
  have he : (∑ i ∈ ((Finset.univ : Finset ι).erase u).erase v, f i) =
      ∑ i ∈ ((Finset.univ : Finset ι).erase u).erase v, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hsame i (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      (Finset.mem_erase.mp hi).1
  have hf1 := Finset.sum_erase_add Finset.univ f (Finset.mem_univ u)
  have hg1 := Finset.sum_erase_add Finset.univ g (Finset.mem_univ u)
  have hf2 := Finset.sum_erase_add (Finset.univ.erase u) f hv
  have hg2 := Finset.sum_erase_add (Finset.univ.erase u) g hv
  linarith

theorem chainEnergy_two_edge_comparison (N : ℕ) (p q : Fin (N + 1) → Phase)
    (i j : Fin N) (hji : j.succ = i.castSucc)
    (hsame : ∀ k, k ≠ i.castSucc → p k = q k)
    (hle : chainEnergy N p ≤ chainEnergy N q) :
    chainEdgeEnergy (p j.castSucc) (p j.succ) +
      chainEdgeEnergy (p i.castSucc) (p i.succ) ≤
    chainEdgeEnergy (q j.castSucc) (q j.succ) +
      chainEdgeEnergy (q i.castSucc) (q i.succ) := by
  have hij : j ≠ i := by
    intro he
    have hv := congrArg Fin.val hji
    rw [he] at hv
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  apply two_term_sum_comparison
    (fun k : Fin N => chainEdgeEnergy (p k.castSucc) (p k.succ))
    (fun k : Fin N => chainEdgeEnergy (q k.castSucc) (q k.succ)) j i hij
  · intro k hkj hki
    have hl : k.castSucc ≠ i.castSucc := by
      intro he
      exact hki (Fin.castSucc_injective N he)
    have hr : k.succ ≠ i.castSucc := by
      intro he
      rw [← hji] at he
      exact hkj (Fin.succ_injective N he)
    rw [hsame _ hl, hsame _ hr]
  · exact hle

theorem admissibleChain_minimizer_midpoint (K B : Set Phase) (hB : Convex ℝ B)
    (N : ℕ) (x y : Phase) (δ ε : ℝ) (hεδ : ε < δ)
    (hloc : ∀ b ∈ K ∩ B, Convex ℝ (K ∩ ball b δ))
    (p : Fin (N + 1) → Phase) (hp : p ∈ admissibleChain (K ∩ B) N x y ε)
    (hmin : ∀ q ∈ admissibleChain (K ∩ B) N x y ε, chainEnergy N p ≤ chainEnergy N q)
    (i j : Fin N) (hji : j.succ = i.castSucc) :
    p i.castSucc = (1 / 2 : ℝ) • (p j.castSucc + p i.succ) := by
  classical
  obtain ⟨hpmem, hpx, hpy, hpedges⟩ := hp
  have hij : j ≠ i := by
    intro he
    have hv := congrArg Fin.val hji
    rw [he] at hv
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  have hjl : j.castSucc ≠ i.castSucc := fun he => hij (Fin.castSucc_injective N he)
  have hir : i.succ ≠ i.castSucc := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  have hzero : (0 : Fin (N + 1)) ≠ i.castSucc := by
    intro he
    have hv := congrArg Fin.val hji
    have hz := congrArg Fin.val he
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero] at hv hz
    omega
  have hlast : Fin.last N ≠ i.castSucc := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  let m := (1 / 2 : ℝ) • (p j.castSucc + p i.succ)
  have hm := local_chain_midpoint_admissible K B hB
    (p j.castSucc) (p i.castSucc) (p i.succ) (hpmem _) (hpmem _)
    δ ε hεδ (by simpa only [hji] using hpedges j) (hpedges i) (hloc _ (hpmem _))
  let q := Function.update p i.castSucc m
  have hsame : ∀ k, k ≠ i.castSucc → p k = q k := by
    intro k hk
    exact (Function.update_of_ne hk m p).symm
  have hq : q ∈ admissibleChain (K ∩ B) N x y ε := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k = i.castSucc
      · simpa only [hk, q, Function.update_self] using hm.1
      · rw [← hsame k hk]
        exact hpmem k
    · rw [← hsame 0 hzero]
      exact hpx
    · rw [← hsame _ hlast]
      exact hpy
    · intro k
      by_cases hkj : k = j
      · subst k
        simpa only [hji, q, Function.update_self, Function.update_of_ne hjl] using hm.2.1
      · by_cases hki : k = i
        · subst k
          simpa only [q, Function.update_self, Function.update_of_ne hir] using hm.2.2
        · have hl : k.castSucc ≠ i.castSucc := fun he => hki (Fin.castSucc_injective N he)
          have hr : k.succ ≠ i.castSucc := by
            intro he
            rw [← hji] at he
            exact hkj (Fin.succ_injective N he)
          rw [← hsame _ hl, ← hsame _ hr]
          exact hpedges k
  have he := chainEnergy_two_edge_comparison N p q i j hji hsame (hmin q hq)
  rw [hji] at he
  have he' : chainEdgeEnergy (p j.castSucc) (p i.castSucc) +
      chainEdgeEnergy (p i.castSucc) (p i.succ) ≤
      chainEdgeEnergy (p j.castSucc) m + chainEdgeEnergy m (p i.succ) := by
    simpa only [q, Function.update_self, Function.update_of_ne hjl,
      Function.update_of_ne hir] using he
  exact chain_midpoint_of_minimal_energy _ _ _ he'

theorem finite_midpoint_chain_affine (N : ℕ) (hN : 0 < N) (p : Fin (N + 1) → Phase)
    (hmid : ∀ i j : Fin N, j.succ = i.castSucc →
      p i.castSucc = (1 / 2 : ℝ) • (p j.castSucc + p i.succ)) :
    ∃ d : Phase, ∀ k : Fin (N + 1), p k = p 0 + (k.val : ℝ) • d := by
  let d := p ⟨1, by omega⟩ - p 0
  have hd : ∀ n (hn : n < N),
      p ⟨n + 1, by omega⟩ - p ⟨n, by omega⟩ = d := by
    intro n
    induction n with
    | zero =>
      intro hn
      rfl
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hm := hmid ⟨n + 1, hn⟩ ⟨n, by omega⟩ (Fin.ext rfl)
      ext l
      have hi' := congrFun hi l
      have hm' := congrFun hm l
      change p ⟨n + 1, by omega⟩ l =
        (1 / 2 : ℝ) * (p ⟨n, by omega⟩ l + p ⟨n + 1 + 1, by omega⟩ l) at hm'
      simp only [Pi.sub_apply] at hi' ⊢
      nlinarith
  have haff : ∀ n (hn : n ≤ N), p ⟨n, by omega⟩ = p 0 + (n : ℝ) • d := by
    intro n
    induction n with
    | zero =>
      intro hn
      simp
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hh := hd n (by omega)
      ext l
      have hi' := congrFun hi l
      have hh' := congrFun hh l
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
        Nat.cast_add, Nat.cast_one] at hi' hh' ⊢
      nlinarith
  exact ⟨d, fun k => haff k.val (by omega)⟩

theorem affine_chain_convex_combinations_mem (K : Set Phase) (N : ℕ) (hN : 0 < N)
    (p : Fin (N + 1) → Phase) (d : Phase)
    (haff : ∀ k, p k = p 0 + (k.val : ℝ) • d)
    (hpmem : ∀ k, p k ∈ K) (δ ε : ℝ) (hδ : 0 < δ) (hεδ : ε < δ)
    (hedge : ∀ i : Fin N, dist (p i.castSucc) (p i.succ) ≤ ε)
    (hloc : ∀ k, Convex ℝ (K ∩ ball (p k) δ))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • p 0 + b • p (Fin.last N) ∈ K := by
  by_cases hb1 : b = 1
  · have ha0 : a = 0 := by linarith
    simpa only [ha0, hb1, zero_smul, one_smul, zero_add] using hpmem (Fin.last N)
  have hble : b ≤ 1 := by linarith
  have hblt : b < 1 := lt_of_le_of_ne hble hb1
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hbN : 0 ≤ b * (N : ℝ) := mul_nonneg hb hNR.le
  let n := Nat.floor (b * (N : ℝ))
  have hn : n < N := (Nat.floor_lt hbN).mpr (by nlinarith)
  let i : Fin N := ⟨n, hn⟩
  let t : ℝ := b * (N : ℝ) - n
  have ht0 : 0 ≤ t := sub_nonneg.mpr (Nat.floor_le hbN)
  have ht1 : t ≤ 1 := by
    have hh := Nat.lt_floor_add_one (b * (N : ℝ))
    dsimp [t, n]
    linarith
  have hleft : p i.castSucc ∈ K ∩ ball (p i.castSucc) δ :=
    ⟨hpmem _, mem_ball_self hδ⟩
  have hright : p i.succ ∈ K ∩ ball (p i.castSucc) δ := by
    refine ⟨hpmem _, ?_⟩
    rw [mem_ball, dist_comm]
    exact (hedge i).trans_lt hεδ
  have hmem := (hloc i.castSucc) hleft hright (sub_nonneg.mpr ht1) ht0
    (show (1 - t) + t = 1 by ring)
  have heq : a • p 0 + b • p (Fin.last N) =
      (1 - t) • p i.castSucc + t • p i.succ := by
    rw [haff (Fin.last N), haff i.castSucc, haff i.succ]
    ext l
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Fin.val_last, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    dsimp [t, i]
    ring
  rw [heq]
  exact hmem.1

theorem closed_preconnected_locally_convex_direct (K : Set Phase)
    (hclosed : IsClosed K) (hconn : IsPreconnected K)
    (hloc : ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U)) :
    Convex ℝ K := by
  intro x hx y hy a b ha hb hab
  have hpc := locallyConvexSet_isPathConnected K hconn ⟨x, hx⟩ hloc
  obtain ⟨γ, hγK⟩ := hpc.joinedIn x hx y hy
  obtain ⟨R, hR⟩ := (isCompact_range γ.continuous).isBounded.subset_closedBall x
  let B := closedBall x R
  let C := K ∩ B
  have hC : IsCompact C := (isCompact_closedBall x R).inter_left hclosed
  obtain ⟨δ, hδ, hδconv⟩ := locallyConvexSet_uniform_radius K C hC inter_subset_left hloc
  have hγC : ∀ t, γ t ∈ C := fun t => ⟨hγK t, hR (mem_range_self t)⟩
  obtain ⟨N, hN, p₀, hp₀x, hp₀y, hp₀C, hp₀edge⟩ :=
    continuous_path_small_chain C γ γ.continuous hγC (δ / 2) (by linarith)
  have hne : (admissibleChain C N x y (δ / 2)).Nonempty := by
    refine ⟨p₀, hp₀C, hp₀x.trans γ.source, hp₀y.trans γ.target, ?_⟩
    intro i
    exact (hp₀edge i).le
  obtain ⟨p, hp, hmin⟩ := admissibleChain_exists_energy_minimizer C hC N x y (δ / 2) hne
  have hmid : ∀ i j : Fin N, j.succ = i.castSucc →
      p i.castSucc = (1 / 2 : ℝ) • (p j.castSucc + p i.succ) := by
    intro i j hji
    exact admissibleChain_minimizer_midpoint K B (convex_closedBall x R) N x y δ (δ / 2)
      (by linarith) hδconv p hp hmin i j hji
  obtain ⟨d, hd⟩ := finite_midpoint_chain_affine N hN p hmid
  obtain ⟨hpmem, hpx, hpy, hpedges⟩ := hp
  have hm := affine_chain_convex_combinations_mem K N hN p d hd
    (fun k => (hpmem k).1) δ (δ / 2) hδ (by linarith) hpedges
    (fun k => hδconv _ (hpmem k)) a b ha hb hab
  simpa only [hpx, hpy] using hm

end BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution (K : Set Phase)
    (hclosed : IsClosed K) (hconn : IsPreconnected K)
    (hloc : ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U)) :
    Convex ℝ K :=
  closed_preconnected_locally_convex_direct K hclosed hconn hloc
