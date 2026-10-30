-- Prove2me | solution 1 for DerivativeChainClusterAnchor.source_cluster_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:23:17.483725+00:00
-- url     : https://prove2.me/submissions/7ea55e29-7a37-437f-be1f-342a00950948

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterSubsetProduct
import Definitions.Def_DerivativeChainAnalytic_ClusterTail
import Theorems.Thm_DerivativeChainClusterAnchor_finite_block_summability
import Theorems.Thm_DerivativeChainClusterAnchor_integer_block_root_bound
import Theorems.Thm_DerivativeChainClusterAnchor_ordinaryRow_cluster_envelope
import Theorems.Thm_DerivativeChainClusterAnchor_ordinaryRow_eval_zero_of_exact_cluster
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace DerivativeChainClusterAnchor

theorem block_monotone_envelope (α : ℝ) (hα : 0 ≤ α) (m r j : ℕ)
    (hr : 0 < r) (hj : 0 < j) (hm : j*r ≤ m) :
    (1+α*(m:ℝ))^((r:ℝ)/(m:ℝ)) ≤ (1+α*(j:ℝ)*(r:ℝ))^((j:ℝ)⁻¹) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hjR : (0:ℝ) < j := by exact_mod_cast hj
  have hmR : (j:ℝ)*(r:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := lt_of_lt_of_le (mul_pos hjR hrR) hmR
  have hratio : 1 ≤ (m:ℝ)/((j:ℝ)*(r:ℝ)) := (one_le_div (mul_pos hjR hrR)).mpr hmR
  have hterm : 0 ≤ α*(j:ℝ)*(r:ℝ) := by positivity
  have hbern := one_add_mul_self_le_rpow_one_add
    (by linarith : (-1:ℝ) ≤ α*(j:ℝ)*(r:ℝ)) hratio
  have he : 1+(m:ℝ)/((j:ℝ)*(r:ℝ))*(α*(j:ℝ)*(r:ℝ))=1+α*(m:ℝ) := by
    field_simp
  rw [he] at hbern
  calc
    _ ≤ ((1+α*(j:ℝ)*(r:ℝ))^((m:ℝ)/((j:ℝ)*(r:ℝ))))^((r:ℝ)/(m:ℝ)) :=
      Real.rpow_le_rpow (by positivity) hbern (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      field_simp

theorem block_envelope_bound (α : ℝ) (hα : 0 ≤ α) (m r j : ℕ)
    (hr : 0 < r) (hj : 2 ≤ j) (hm : j*r ≤ m) :
    (1+α*(m:ℝ))^((r:ℝ)/(m:ℝ)) ≤
      2+4*Real.sqrt (α*(r:ℝ))/((j:ℝ)*Real.sqrt (j:ℝ)) := by
  have h := integer_block_root_bound j hj (α*(r:ℝ)) (by positivity)
  have hmono := block_monotone_envelope α hα m r j hr (by omega) hm
  have he : 1+α*(j:ℝ)*(r:ℝ)=1+(α*(r:ℝ))*(j:ℝ) := by ring
  rw [he] at hmono
  exact hmono.trans h





end DerivativeChainClusterAnchor


set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Finset Polynomial
namespace DerivativeChainClusterAnchor
noncomputable section



theorem source_anchor_radius_bound {n m r : ℕ} (a : Fin n → ℂ) (c : ℂ)
    (O : Finset (Fin n)) (hn : 0 < n) (hm : m ≤ n) (hm0 : 0 < m) (hO : O.card ≤ r)
    (ε D : ℝ) (hε : 0 < ε) (hεD : ε ≤ D)
    (hnear : ∀ i, i ∉ O → ‖c-a i‖ ≤ ε) (hfar : ∀ i, i ∈ O → ‖c-a i‖ ≤ D) :
    anchorRadius a c m ≤ ε*(1+D*(m:ℝ)/((n:ℝ)*ε))^((r:ℝ)/(m:ℝ)) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm0
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hD : 0 ≤ D := hε.le.trans hεD
  have hbase : 0 ≤ 1+D*(m:ℝ)/((n:ℝ)*ε) := by positivity
  have hbound := ordinaryRow_cluster_envelope a c O hn hm hO ε D hε hεD hnear hfar
  calc
    _ ≤ (ε^m*(1+D*(m:ℝ)/((n:ℝ)*ε))^r)^((m:ℝ)⁻¹) :=
      Real.rpow_le_rpow (norm_nonneg _) hbound (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (pow_nonneg hε.le _) (pow_nonneg hbase _),
        Real.pow_rpow_inv_natCast hε.le hm0.ne',← Real.rpow_natCast_mul hbase]
      rfl

theorem tail_bucket_card_bound (n r j : ℕ) (hr : 0 < r) :
    ((Finset.Icc (2*r+1) n).filter (fun m => m/r=j)).card ≤ r := by
  have hsub : (Finset.Icc (2*r+1) n).filter (fun m => m/r=j) ⊆ Finset.Ico (j*r) ((j+1)*r) := by
    intro m hm
    have hq : m/r=j := (Finset.mem_filter.mp hm).2
    have he := Nat.mod_add_div m r
    rw [hq] at he
    have hmod := Nat.mod_lt m hr
    simp only [Finset.mem_Ico]
    constructor <;> nlinarith [Nat.zero_le (m%r)]
  simpa [Nat.card_Ico,Nat.add_mul] using Finset.card_le_card hsub

theorem reciprocal_block_sum_Icc (n : ℕ) :
    (∑ j ∈ Finset.Icc 2 n, 1/((j:ℝ)*Real.sqrt (j:ℝ))) ≤ 2 := by
  have hset : Finset.Icc 2 n=Finset.Ico 2 (n+1) := by
    ext j
    simp only [Finset.mem_Icc,Finset.mem_Ico]
    omega
  rw [hset,Finset.sum_Ico_eq_sum_range]
  simpa only [Nat.cast_add,Nat.cast_ofNat,add_comm] using finite_block_summability (n+1-2)

theorem tail_reciprocal_bucket_sum (n r : ℕ) (hr : 0 < r) :
    (∑ m ∈ Finset.Icc (2*r+1) n,
      1/(((m/r:ℕ):ℝ)*Real.sqrt ((m/r:ℕ):ℝ))) ≤ 2*(r:ℝ) := by
  let S := Finset.Icc (2*r+1) n
  let f : ℕ → ℝ := fun j => 1/((j:ℝ)*Real.sqrt (j:ℝ))
  have hmap : ∀ m ∈ S, m/r ∈ Finset.Icc 2 n := by
    intro m hm
    have hmem := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hr).mpr (by omega),
      (Nat.div_le_self m r).trans hmem.2⟩
  change (∑ m ∈ S, f (m/r)) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  have hterm (j : ℕ) : (∑ m ∈ S with m/r=j, f (m/r)) ≤ (r:ℝ)*f j := by
    have he : (∑ m ∈ S with m/r=j, f (m/r)) =
        (((S.filter (fun m => m/r=j)).card:ℕ):ℝ)*f j := by
      calc
        _ = ∑ m ∈ S with m/r=j, f j := Finset.sum_congr rfl
          (fun m hm => by rw [(Finset.mem_filter.mp hm).2])
        _ = _ := by simp
    rw [he]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast tail_bucket_card_bound n r j hr) (by dsimp [f]; positivity)
  calc
    _ ≤ ∑ j ∈ Finset.Icc 2 n, (r:ℝ)*f j := Finset.sum_le_sum (fun j _ => hterm j)
    _ = (r:ℝ)*(∑ j ∈ Finset.Icc 2 n, f j) := (Finset.mul_sum _ _ _).symm
    _ ≤ (r:ℝ)*2 := mul_le_mul_of_nonneg_left (reciprocal_block_sum_Icc n) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem positive_cluster_tail_sum {n r : ℕ} (a : Fin n → ℂ) (c : ℂ)
    (O : Finset (Fin n)) (hn : 0 < n) (hr : 0 < r) (hO : O.card ≤ r)
    (ε D : ℝ) (hε : 0 < ε) (hεD : ε ≤ D)
    (hnear : ∀ i, i ∉ O → ‖c-a i‖ ≤ ε) (hfar : ∀ i, i ∈ O → ‖c-a i‖ ≤ D) :
    (∑ m ∈ Finset.Icc (2*r+1) n, anchorRadius a c m) ≤
      2*(n:ℝ)*ε+8*ε*(r:ℝ)*Real.sqrt (D*(r:ℝ)/((n:ℝ)*ε)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hD : 0 ≤ D := hε.le.trans hεD
  let B : ℝ := D*(r:ℝ)/((n:ℝ)*ε)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (m : ℕ) (hm : m ∈ Finset.Icc (2*r+1) n) :
      anchorRadius a c m ≤ 2*ε+4*ε*Real.sqrt B*
        (1/(((m/r:ℕ):ℝ)*Real.sqrt ((m/r:ℕ):ℝ))) := by
    have hmem := Finset.mem_Icc.mp hm
    have hj : 2 ≤ m/r := (Nat.le_div_iff_mul_le hr).mpr (by omega)
    have hbase := source_anchor_radius_bound a c O hn hmem.2 (by omega) hO ε D hε hεD hnear hfar
    have hb := block_envelope_bound (D/((n:ℝ)*ε)) (by positivity) m r (m/r) hr hj (Nat.div_mul_le_self m r)
    have he : 1+D*(m:ℝ)/((n:ℝ)*ε)=1+(D/((n:ℝ)*ε))*(m:ℝ) := by ring
    rw [he] at hbase
    have h := hbase.trans (mul_le_mul_of_nonneg_left hb hε.le)
    have heB : D/((n:ℝ)*ε)*(r:ℝ)=B := by dsimp [B]; ring
    rw [heB] at h
    exact h.trans_eq (by ring)
  have hsum := Finset.sum_le_sum hpoint
  have hcard : ((Finset.Icc (2*r+1) n).card:ℝ) ≤ n := by
    rw [Nat.card_Icc]
    exact_mod_cast (by omega : n+1-(2*r+1) ≤ n)
  calc
    _ ≤ ∑ m ∈ Finset.Icc (2*r+1) n, (2*ε+4*ε*Real.sqrt B*
        (1/(((m/r:ℕ):ℝ)*Real.sqrt ((m/r:ℕ):ℝ)))) := hsum
    _ = 2*ε*((Finset.Icc (2*r+1) n).card:ℝ)+4*ε*Real.sqrt B*
        (∑ m ∈ Finset.Icc (2*r+1) n, 1/(((m/r:ℕ):ℝ)*Real.sqrt ((m/r:ℕ):ℝ))) := by
      rw [Finset.sum_add_distrib,Finset.sum_const,← Finset.mul_sum]
      simp only [nsmul_eq_mul]
      ring
    _ ≤ 2*ε*(n:ℝ)+4*ε*Real.sqrt B*(2*(r:ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hcard (by positivity))
        (mul_le_mul_of_nonneg_left (tail_reciprocal_bucket_sum n r hr) (by positivity))
    _ = _ := by dsimp [B]; ring

theorem nat_three_halves (r : ℕ) (hr : 0 < r) :
    (r:ℝ)^((3:ℝ)/2)=(r:ℝ)*Real.sqrt (r:ℝ) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  rw [show (3:ℝ)/2=1+1/2 by norm_num,Real.rpow_add hrR,Real.rpow_one,Real.sqrt_eq_rpow]



end
end DerivativeChainClusterAnchor


set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Finset Polynomial
open DerivativeChainClusterAnchor
















theorem solution {n r : ℕ} (a : Fin n → ℂ) (c : ℂ)
    (O : Finset (Fin n)) (hr : 0 < r) (hcut : 2*r < n) (hO : O.card ≤ r)
    (ε D : ℝ) (hε : 0 ≤ ε) (hεD : ε ≤ D)
    (hnear : ∀ i, i ∉ O → ‖a i-c‖ ≤ ε) (hall : ∀ i, ‖a i-c‖ ≤ D) :
    (∑ m ∈ Finset.Icc (2*r+1) n, _root_.DerivativeChainClusterAnchor.anchorRadius a c m) ≤
      2*(n:ℝ)*ε+8*(r:ℝ)^((3:ℝ)/2)*Real.sqrt (D*ε/(n:ℝ)) := by
  have hn : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  by_cases heps : ε=0
  · subst ε
    have hzero (m : ℕ) (hm : m ∈ Finset.Icc (2*r+1) n) : _root_.DerivativeChainClusterAnchor.anchorRadius a c m=0 := by
      have hmem := Finset.mem_Icc.mp hm
      have heval := _root_.DerivativeChainClusterAnchor.ordinaryRow_eval_zero_of_exact_cluster a c O hmem.2 hO (by omega)
        (fun i hi => (sub_eq_zero.mp (norm_eq_zero.mp
          (le_antisymm (hnear i hi) (norm_nonneg _)))))
      rw [_root_.DerivativeChainClusterAnchor.anchorRadius,heval,norm_zero,Real.zero_rpow (by
        have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
        positivity : (m:ℝ)⁻¹ ≠ 0)]
    rw [Finset.sum_eq_zero hzero]
    simp
  · have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm heps)
    have hD : 0 ≤ D := hε.trans hεD
    have hradB : 0 ≤ D*(r:ℝ)/((n:ℝ)*ε) := by positivity
    have hradA : 0 ≤ D*ε/(n:ℝ) := by positivity
    have hscale : ε*(r:ℝ)*Real.sqrt (D*(r:ℝ)/((n:ℝ)*ε)) =
        (r:ℝ)*Real.sqrt (r:ℝ)*Real.sqrt (D*ε/(n:ℝ)) := by
      apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
      simp only [mul_pow,Real.sq_sqrt hradB,Real.sq_sqrt hradA,Real.sq_sqrt (Nat.cast_nonneg r)]
      field_simp <;> ring
    have hp := _root_.DerivativeChainClusterAnchor.positive_cluster_tail_sum a c O hn hr hO ε D hεpos hεD
      (fun i hi => by simpa only [norm_sub_rev] using hnear i hi)
      (fun i _ => by simpa only [norm_sub_rev] using hall i)
    refine hp.trans_eq ?_
    rw [_root_.DerivativeChainClusterAnchor.nat_three_halves r hr]
    nlinarith only [hscale]
