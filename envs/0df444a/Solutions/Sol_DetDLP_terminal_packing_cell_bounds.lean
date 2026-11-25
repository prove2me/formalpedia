-- Prove2me | solution 1 for DetDLP.terminal_packing_cell_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T12:01:54.539502+00:00
-- url     : https://prove2.me/submissions/eba4dabc-ef0a-42ba-9106-9597a10a19c4

import Theorems.Thm_DetDLP_joint_terminal_edge_partition

namespace DetDLP.EdgeLabelPartition
open Finset
private def left (G : BipartiteMultigraph) (e : Fin G.nE) :=
  if G.side (G.endpoints e).1 then (G.endpoints e).2 else (G.endpoints e).1
private def right (G : BipartiteMultigraph) (e : Fin G.nE) :=
  if G.side (G.endpoints e).1 then (G.endpoints e).1 else (G.endpoints e).2

private def edgeCell (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) (e : Fin G.nE) :=
  (L (left G e),L (right G e))

def cellSize (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) (c : Fin q × Fin q) : ℕ :=
  ∑ e, if edgeCell G L e = c then 1 else 0

theorem cell_sum (G : BipartiteMultigraph) {q : ℕ} (L : Fin G.nV → Fin q) :
    ∑ c, cellSize G L c = G.nE := by
  unfold cellSize
  rw [sum_comm]; simp


end DetDLP.EdgeLabelPartition

namespace DetDLP.TerminalCellBounds
open Finset EdgeLabelPartition

private def hist {m : ℕ} {γ : Type*} [DecidableEq γ] (f : Fin m → γ) (g : γ) : ℕ :=
  ∑ x, if f x = g then 1 else 0

private theorem hist_sum {m : ℕ} {γ : Type*} [DecidableEq γ] [Fintype γ] (f : Fin m → γ) :
    ∑ g, hist f g = m := by unfold hist; rw [sum_comm]; simp

private theorem hist_collision {m : ℕ} {γ : Type*} [DecidableEq γ] [Fintype γ] (f : Fin m → γ) :
    ∑ g, hist f g^2 = ∑ x, ∑ y, if f x = f y then 1 else 0 := by
  have hp (g : γ) : hist f g^2 = ∑ x, if f x = g then hist f g else 0 := by
    calc
      _ = (∑ x,if f x = g then 1 else 0)*hist f g := by rw [pow_two]; rfl
      _ = _ := by rw [sum_mul]; simp [ite_mul]
  simp_rw [hp]; rw [sum_comm]; simp only [sum_ite_eq,mem_univ,if_true,hist]
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro y _
  by_cases h : f x = f y <;> simp_all [eq_comm]

private theorem centered {γ : Type*} [Fintype γ] (X : γ → ℕ) (K M : ℕ)
    (hK : Fintype.card γ = K) (hM : ∑ i,X i = M) :
    ∑ i, ((K:ℤ)*(X i:ℤ)-M)^2 = (K:ℤ)*((K:ℤ)*(∑ i, (X i:ℤ)^2)-(M:ℤ)^2) := by
  have hs : (∑ i, (X i:ℤ)) = (M:ℤ) := by exact_mod_cast hM
  calc
    _ = ∑ i, ((K:ℤ)^2 * (X i:ℤ)^2 -(2*(K:ℤ)*M)*(X i:ℤ)+(M:ℤ)^2) := by
      apply sum_congr rfl; intros; ring
    _ = _ := by rw [sum_add_distrib,sum_sub_distrib,← mul_sum,← mul_sum,hs,sum_const,card_univ,hK,nsmul_eq_mul]; ring

private theorem center_bounds {γ : Type*} [Fintype γ] (X : γ → ℕ) (K M : ℕ)
    (hK : Fintype.card γ = K) (hM : ∑ i,X i = M) (hpos : 0 < K) :
    let V : ℤ := (K:ℤ)*(∑ i, (X i:ℤ)^2)-(M:ℤ)^2
    0 ≤ V ∧ ∀ i, ((K:ℤ)*(X i:ℤ)-M)^2 ≤ K*V := by
  intro V
  have hc := centered X K M hK hM
  change _ = (K:ℤ)*V at hc
  constructor
  · have h : 0 ≤ (K:ℤ)*V := hc ▸ sum_nonneg (fun _ _ => sq_nonneg _)
    have hk : 0 < (K:ℤ) := by exact_mod_cast hpos
    exact nonneg_of_mul_nonneg_right h hk
  · intro i; rw [← hc]; exact single_le_sum (f := fun j => ((K:ℤ)*(X j:ℤ)-M)^2) (fun _ _ => sq_nonneg _) (mem_univ i)

def legCount {a b n : ℕ} (L : Fin n → Fin (64^a)) (host : Fin b → Fin n) (i : Fin a) (g : Fin 64) : ℕ :=
  hist (fun x => finFunctionFinEquiv.symm (L (host x)) i) g

/-- Both packet capacities hold for one assignment of the labels of all old vertices. -/
theorem packing_caps (G : BipartiteMultigraph) (a : ℕ) {b : ℕ} (host : Fin b → Fin G.nV) (τ : ℕ)
    (ht : ∀ x, (univ.filter fun y => host x = host y).card ≤ τ)
    (hb : 0 < b*τ) (hm : 0 < G.nE*G.maxDeg)
    (hsize : (a+2)*(64^a)^4*G.maxDeg ≤ G.nE) :
    ∃ L : Fin G.nV → Fin (64^a),
      (∀ c, (64^a)^2*cellSize G L c ≤ 2*G.nE) ∧
      (∀ i g, 32*legCount L host i g ≤ b+512*(a+2)*τ) := by
  obtain ⟨L,hL⟩ := joint_terminal_edge_partition G 64 a host τ (b*τ) (G.nE*G.maxDeg) ht
  refine ⟨L,?_⟩
  let K : ℕ := (64^a)^2
  let X := cellSize G L
  let Y := legCount L host
  let E : ℤ := K*(∑ c, (X c:ℤ)^2)-(G.nE:ℤ)^2
  let V (i : Fin a) : ℤ := 64*(∑ g, (Y i g:ℤ)^2)-(b:ℤ)^2
  let T := ∑ i, V i
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨hE,hX⟩ := center_bounds X K G.nE (by simp [K,pow_two]) (cell_sum G L) hK
  change 0 ≤ E at hE
  change ∀ c, ((K:ℤ)*(X c:ℤ)-G.nE)^2 ≤ K*E at hX
  have hv (i : Fin a) := center_bounds (Y i) 64 b (by simp) (hist_sum _) (by decide)
  have hV (i : Fin a) : 0 ≤ V i := (hv i).1
  have hT : 0 ≤ T := sum_nonneg (fun i _ => hV i)
  have hY (i : Fin a) (g : Fin 64) : (64*(Y i g:ℤ)-b)^2 ≤ 64*T :=
    ((hv i).2 g).trans (mul_le_mul_of_nonneg_left (single_le_sum (fun j _ => hV j) (mem_univ i)) (by decide))
  have hve : T = 64*(∑ i, ∑ g, (Y i g:ℤ)^2)-(a:ℤ)*(b:ℤ)^2 := by
    dsimp only [T,V]; rw [sum_sub_distrib,←mul_sum,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  have htcol : (∑ i : Fin a, ∑ x : Fin b, ∑ y : Fin b,
        if finFunctionFinEquiv.symm (L (host x)) i = finFunctionFinEquiv.symm (L (host y)) i then 1 else 0) =
      ∑ i, ∑ g, Y i g^2 := by
    apply sum_congr rfl; intro i _; exact (hist_collision _).symm
  change 64*K*((b*τ)*(∑ c,X c^2)+(G.nE*G.maxDeg)*_) ≤
      64*(b*τ)*(G.nE^2+2*G.nE*G.maxDeg*K)+(G.nE*G.maxDeg)*a*b*K*(b+τ*64) at hL
  rw [htcol] at hL
  have hraw : (64:ℤ)*K*((b:ℤ)*τ*(∑ c,(X c:ℤ)^2) +
        ((G.nE:ℤ)*G.maxDeg)*(∑ i,∑ g,(Y i g:ℤ)^2)) ≤
      64*((b:ℤ)*τ)*((G.nE:ℤ)^2+2*G.nE*G.maxDeg*K)+((G.nE:ℤ)*G.maxDeg)*a*b*K*(b+τ*64) := by
    exact_mod_cast hL
  let w : ℤ := (b:ℤ)*τ
  let v : ℤ := (G.nE:ℤ)*G.maxDeg
  have hw : 0 < w := by dsimp only [w]; exact_mod_cast hb
  have hpos : 0 < v := by dsimp only [v]; exact_mod_cast hm
  have kpos : 0 < (K:ℤ) := by exact_mod_cast hK
  have comb : 64*w*E + (K:ℤ)*v*T ≤ 64*(K:ℤ)*w*v*((a:ℤ)+2) := by
    dsimp only [E,w,v]; rw [hve]; nlinarith only [hraw]
  have hecap : E ≤ K*v*((a:ℤ)+2) := by
    apply le_of_mul_le_mul_left (a := 64*w) _ (by positivity)
    nlinarith only [comb,mul_nonneg (mul_nonneg kpos.le hpos.le) hT]
  have htcap : T ≤ 64*w*((a:ℤ)+2) := by
    apply le_of_mul_le_mul_left (a := (K:ℤ)*v) _ (by positivity)
    nlinarith only [comb,mul_nonneg (mul_nonneg (by decide : (0:ℤ) ≤ 64) hw.le) hE]
  constructor
  · intro c
    have hM : ((a:ℤ)+2)*(K:ℤ)^2*G.maxDeg ≤ G.nE := by
      have hK4 : K^2 = (64^a)^4 := by dsimp only [K]; ring
      exact_mod_cast (show (a+2)*K^2*G.maxDeg ≤ G.nE by rw [hK4]; exact hsize)
    have hx' := (hX c).trans (mul_le_mul_of_nonneg_left hecap kpos.le)
    have hbound := mul_le_mul_of_nonneg_left hM (show 0 ≤ (G.nE:ℤ) by positivity)
    have hnat : (K:ℤ)*(X c:ℤ) ≤ 2*G.nE := by
      by_contra! hi
      dsimp only [v] at hx'
      have hp : 0 < (K:ℤ)*(X c:ℤ) := lt_of_le_of_lt (by positivity : (0:ℤ) ≤ 2*G.nE) hi
      nlinarith only [hx',hbound,mul_pos (sub_pos.mpr hi) hp]
    exact_mod_cast hnat
  · intro i g
    have hyy := (hY i g).trans (mul_le_mul_of_nonneg_left htcap (by decide : (0:ℤ) ≤ 64))
    dsimp only [w] at hyy
    have hh : 32*(Y i g:ℤ) ≤ b+512*((a:ℤ)+2)*τ := by
      by_contra! hi
      have hz : 0 < 64*(Y i g:ℤ)-b+(b+1024*((a:ℤ)+2)*τ) := by nlinarith
      nlinarith only [hyy,sq_nonneg ((b:ℤ)-1024*((a:ℤ)+2)*τ),
        mul_pos (show 0 < 64*(Y i g:ℤ)-b-(b+1024*((a:ℤ)+2)*τ) by linarith) hz]
    exact_mod_cast hh
end DetDLP.TerminalCellBounds

open DetDLP

theorem solution (G : BipartiteMultigraph) (a : ℕ) {b : ℕ} (host : Fin b → Fin G.nV) (τ : ℕ)
    (ht : ∀ x, (Finset.univ.filter fun y => host x = host y).card ≤ τ)
    (hb : 0 < b*τ) (hm : 0 < G.nE*G.maxDeg)
    (hsize : (a+2)*(64^a)^4*G.maxDeg ≤ G.nE) :
    let l := fun e : Fin G.nE => if G.side (G.endpoints e).1 then (G.endpoints e).2 else (G.endpoints e).1
    let r := fun e : Fin G.nE => if G.side (G.endpoints e).1 then (G.endpoints e).1 else (G.endpoints e).2
    ∃ L : Fin G.nV → Fin (64^a),
      (∀ c : Fin (64^a) × Fin (64^a),
        (64^a)^2*(∑ e : Fin G.nE, if (L (l e),L (r e)) = c then 1 else 0) ≤ 2*G.nE) ∧
      (∀ (i : Fin a) (g : Fin 64),
        32*(∑ x : Fin b, if finFunctionFinEquiv.symm (L (host x)) i = g then 1 else 0) ≤ b+512*(a+2)*τ) := by
  exact TerminalCellBounds.packing_caps G a host τ ht hb hm hsize
