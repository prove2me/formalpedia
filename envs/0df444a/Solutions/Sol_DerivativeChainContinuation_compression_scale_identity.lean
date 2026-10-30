-- Prove2me | solution 1 for DerivativeChainContinuation.compression_scale_identity
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:58:23.680652+00:00
-- url     : https://prove2.me/submissions/9a926f76-ea57-4156-9f7f-370257d27a2e

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_CompressionRankTwo
import Definitions.Def_DerivativeChainContinuation_RegularizedGram
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_compression_gram_cyclic
import Theorems.Thm_DerivativeChainContinuation_rank_two_determinant
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators





theorem diagonal_projection_product_entry {n : ℕ} (a : Fin n → ℂ) (i j : Fin n) :
    (diagonal (star a)*centeringProjection n*diagonal a*centeringProjection n) i j =
      (if i=j then star (a i)*a i else 0)-star (a i)*a i/(n:ℂ)-star (a i)*a j/(n:ℂ)+
        star (a i)*(∑ k,a k)/(n:ℂ)^2 := by
  simp only [Matrix.mul_apply,Matrix.diagonal_apply,centeringProjection,Matrix.sub_apply,
    Matrix.one_apply,Matrix.of_apply,Pi.star_apply,ite_mul,mul_ite,zero_mul,mul_zero,
    Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp only [sub_mul,mul_sub,Finset.sum_sub_distrib,ite_mul,mul_ite,zero_mul,mul_zero,
    Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,if_true]
  simp only [← Finset.mul_sum,← Finset.sum_mul]
  split_ifs with h
  · subst j; ring
  · ring

theorem compression_rank_two_update {n : ℕ} (a : Fin n → ℂ) (t : ℝ) :
    diagonal (fun _ => (t:ℂ))+diagonal (star a)*centeringProjection n*diagonal a*centeringProjection n =
      diagonal (fun i => (t:ℂ)+(Complex.normSq (a i):ℂ))+
        compressionUpdateLeft a*compressionUpdateRight a := by
  ext i j
  simp only [Matrix.add_apply]
  rw [diagonal_projection_product_entry]
  simp only [Matrix.diagonal_apply,
    compressionUpdateLeft,compressionUpdateRight,Matrix.mul_apply,Matrix.of_apply,
    Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,Matrix.head_fin_const,
    Complex.normSq_eq_conj_mul_self,Complex.star_def]
  split_ifs with h
  · subst j; ring
  · ring
end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) (t : ℝ)
    (ht : 0 < t) :
    let d := fun i => (t:ℂ)+(Complex.normSq (a i):ℂ);
    (regularizedGram (rootCompression a) t).det =
      (∏ i,d i)*((t:ℂ)/(n:ℂ)^2)*
        ((t:ℂ)*(∑ i,(d i)⁻¹)^2+(∑ i,a i/d i)*(∑ i,star (a i)/d i)) := by
  dsimp only
  let d := fun i => (t:ℂ)+(Complex.normSq (a i):ℂ)
  have hd (i : Fin n) : d i ≠ 0 := by
    have h : 0 < t+Complex.normSq (a i) := add_pos_of_pos_of_nonneg ht (Complex.normSq_nonneg _)
    simpa only [d,← Complex.ofReal_add] using Complex.ofReal_ne_zero.mpr h.ne'
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  let S := ∑ i,(d i)⁻¹
  let M := ∑ i,a i/d i
  let C := ∑ i,star (a i)/d i
  let A := ∑ i,a i
  have hs2 : (∑ i,star (a i)*a i/d i)=(n:ℂ)-(t:ℂ)*S := by
    have he (i : Fin n) : star (a i)*a i/d i=1-(t:ℂ)*(d i)⁻¹ := by
      have hh : d i=(t:ℂ)+star (a i)*a i := by
        simp only [d,Complex.normSq_eq_conj_mul_self,Complex.star_def]
      field_simp [hd i]
      rw [hh]
      ring
    simp only [he,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,S]
  have hs3 : (∑ i,a i*(star (a i)*a i)/d i)=A-(t:ℂ)*M := by
    have he (i : Fin n) : a i*(star (a i)*a i)/d i=a i-(t:ℂ)*(a i/d i) := by
      have hh : d i=(t:ℂ)+star (a i)*a i := by
        simp only [d,Complex.normSq_eq_conj_mul_self,Complex.star_def]
      field_simp [hd i]
      rw [hh]
      ring
    simp only [he,Finset.sum_sub_distrib,← Finset.mul_sum,A,M]
  have h1 : (∑ i,((A/(n:ℂ)-a i)/(n:ℂ))*star (a i)/d i) =
      A/(n:ℂ)^2*C-((n:ℂ)-(t:ℂ)*S)/(n:ℂ) := by
    have he (i : Fin n) : ((A/(n:ℂ)-a i)/(n:ℂ))*star (a i)/d i =
        A/(n:ℂ)^2*(star (a i)/d i)-(star (a i)*a i/d i)/(n:ℂ) := by ring
    simp only [he,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_div,hs2,C]
  have h2 : (∑ i,((A/(n:ℂ)-a i)/(n:ℂ))*(star (a i)*a i)/d i) =
      A/(n:ℂ)^2*((n:ℂ)-(t:ℂ)*S)-(A-(t:ℂ)*M)/(n:ℂ) := by
    have he (i : Fin n) : ((A/(n:ℂ)-a i)/(n:ℂ))*(star (a i)*a i)/d i =
        A/(n:ℂ)^2*(star (a i)*a i/d i)-(a i*(star (a i)*a i)/d i)/(n:ℂ) := by ring
    simp only [he,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_div,hs2,hs3]
  have h3 : (∑ i,(-(n:ℂ)⁻¹)*(star (a i)*a i)/d i)= -((n:ℂ)-(t:ℂ)*S)/(n:ℂ) := by
    calc
      _ = (-(n:ℂ)⁻¹)*(∑ i,star (a i)*a i/d i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [hs2]; ring
  have h4 : (∑ i,(-(n:ℂ)⁻¹)*star (a i)/d i)= -C/(n:ℂ) := by
    simp only [mul_div_assoc,← Finset.mul_sum,C]
    ring
  have he : compressionUpdateLeft a*compressionUpdateRight a =
      Matrix.of (fun i j => star (a i)*((A/(n:ℂ)-a j)/(n:ℂ))+
        (star (a i)*a i)*(-(n:ℂ)⁻¹)) := by
    ext i j
    simp [compressionUpdateLeft,compressionUpdateRight,Matrix.mul_apply,Fin.sum_univ_two,A]
  rw [compression_gram_cyclic hn,compression_rank_two_update,he]
  change (diagonal d+_).det=(∏ i,d i)*((t:ℂ)/(n:ℂ)^2)*((t:ℂ)*S^2+M*C)
  rw [rank_two_determinant d (fun i => star (a i)) (fun i => star (a i)*a i)
    (fun i => (A/(n:ℂ)-a i)/(n:ℂ)) (fun _ => -(n:ℂ)⁻¹) hd,h1,h2,h3,h4]
  field_simp [hnC]
  ring
