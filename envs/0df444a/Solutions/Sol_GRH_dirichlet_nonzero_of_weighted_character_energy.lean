-- Prove2me | solution 1 for GRH.dirichlet_nonzero_of_weighted_character_energy
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:07:36.843643+00:00
-- url     : https://prove2.me/submissions/d8400e3d-e58e-4032-9432-c7eae266d6d6

import Definitions.Def_GRH_WeightedEnergy
import Theorems.Thm_GRH_character_weighted_autocorrelation_identity
import Theorems.Thm_GRH_character_weighted_moment_abel_inequality
import Theorems.Thm_GRH_centered_prefix_character_unit_rows
import Theorems.Thm_GRH_dirichlet_prefix_unit_count_bound
import Theorems.Thm_GRH_dirichlet_abel_bound_of_prefix_envelope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open GRH.WeightedEnergy
open GRH.CharacterMoment (units entry Permutes Rows deviation lastRow)

private lemma bracket (D p t n v : ℕ) (hn : 0<n) (ht : 0<t)
    (lo : (v-1)^t*n^p ≤ D^t) (hi : D^t ≤ v^t*n^p) :
    ((v-1:ℕ):ℝ) ≤ (D:ℝ)*(n:ℝ)^(-((p:ℝ)/t)) ∧
      (D:ℝ)*(n:ℝ)^(-((p:ℝ)/t)) ≤ (v:ℝ) := by
  let z := (n:ℝ)^((p:ℝ)/t)
  have hz : 0 < z := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have power : z^t=(n:ℝ)^p := by
    dsimp [z]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _),div_mul_cancel₀ _
      (Nat.cast_ne_zero.mpr ht.ne'),Real.rpow_natCast]
  have l : (((v-1:ℕ):ℝ)*z)^t ≤ (D:ℝ)^t := by
    rw [mul_pow,power]
    exact_mod_cast lo
  have u : (D:ℝ)^t ≤ ((v:ℝ)*z)^t := by
    rw [mul_pow,power]
    exact_mod_cast hi
  rw [Real.rpow_neg (Nat.cast_nonneg _),← div_eq_mul_inv]
  exact ⟨(le_div_iff₀ hz).2 (le_of_pow_le_pow_left₀ ht.ne' (by positivity) l),
    (div_le_iff₀ hz).2 (le_of_pow_le_pow_left₀ ht.ne' (by positivity) u)⟩

private lemma grouped (g : Data) (F : ℕ → ℝ)
    (hk : ∀ k, g.key ((k+1)%g.Q) ∈ keys g)
    (hW : ∀ i ∈ keys g, g.W i=weightSum g.Q g.M g.u g.key i) :
    ∑ k ∈ Finset.range g.M, F (g.key ((k+1)%g.Q))*(delta g.u k:ℝ) =
      ∑ i ∈ keys g, (g.W i:ℝ)*F i := by
  calc _ = ∑ k ∈ Finset.range g.M, ∑ i ∈ keys g,
             if g.key ((k+1)%g.Q)=i then (delta g.u k:ℝ)*F i else 0 := by
             apply Finset.sum_congr rfl
             intro k _
             simp [Finset.sum_ite_eq,hk k,mul_comm]
       _ = _ := by
             rw [Finset.sum_comm]
             apply Finset.sum_congr rfl
             intro i hi
             rw [hW i hi,weightSum,Nat.cast_sum,Finset.sum_mul]
             apply Finset.sum_congr rfl
             intro k _
             by_cases h : g.key ((k+1)%g.Q)=i <;> simp [h]

private lemma strict_moment (g : Data) (P : ℝ) (hL : 0<g.L)
    (hm : (g.L:ℝ)^(2^g.rows.length)*P^(2*2^g.rows.length) ≤
      ((∑ i ∈ g.I,g.W i*g.scale i:ℕ):ℝ)^(2^g.rows.length)*
        (deviation g.U (lastRow g.T g.rows) g.c:ℝ))
    (test : g.v^(2*2^g.rows.length)*(∑ i ∈ g.I,g.W i*g.scale i)^(2^g.rows.length)*
      deviation g.U (lastRow g.T g.rows) g.c < (budget g)^(2*2^g.rows.length)*g.L^(2^g.rows.length)) :
    (g.v:ℝ)*P < (budget g:ℝ) := by
  let n := 2^g.rows.length
  let H := ∑ i ∈ g.I,g.W i*g.scale i
  let E := deviation g.U (lastRow g.T g.rows) g.c
  have h : (g.v:ℝ)^(2*n)*(H:ℝ)^n*(E:ℝ) < (budget g:ℝ)^(2*n)*(g.L:ℝ)^n := by exact_mod_cast test
  have m : (g.L:ℝ)^n*P^(2*n) ≤ (H:ℝ)^n*(E:ℝ) := hm
  have le := mul_le_mul_of_nonneg_left m (pow_nonneg (Nat.cast_nonneg (α:=ℝ) g.v) (2*n))
  have hr : ((g.v:ℝ)*P)^(2*n)*(g.L:ℝ)^n < (budget g:ℝ)^(2*n)*(g.L:ℝ)^n := by
    rw [mul_pow]
    linarith only [le,h]
  have lpos : 0<(g.L:ℝ)^n := pow_pos (by exact_mod_cast hL) _
  exact lt_of_pow_lt_pow_left₀ (2*n) (Nat.cast_nonneg _) ((mul_lt_mul_iff_left₀ lpos).1 hr)

/-- A single weighted squared-character sum bounds the Abel error throughout the
rectangle for every nonprincipal character at a divisor of the witness period. -/
theorem solution (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ≠1)
    (a b H : ℝ) (hc : Covers d a b H) (s : ℂ) (ha : a ≤ s.re) (hb : s.re ≤ b)
    (hH : |s.im| ≤ H) : χ.LFunction s ≠ 0 := by
  obtain ⟨g,good,hd,hx,hrect⟩ := hc
  obtain ⟨hQ,hD,hp,ht,hw,hL,hR,hphi,hU,perm,hi0,hi1,key0,hkeys,hW,hsc,hT,hrows,htable,hbud,htest⟩ := good
  let : NeZero g.Q := ⟨by omega⟩
  let ψ := DirichletCharacter.changeLevel hd χ
  have hn : ψ ≠ 1 := fun e => hχ ((DirichletCharacter.changeLevel_eq_one_iff hd).1 e)
  let x := (g.p:ℝ)/g.t
  let K := (g.v:ℝ)/g.w
  have hxp : 0 < x := div_pos (by exact_mod_cast hp) (by exact_mod_cast ht)
  have Dpos : 0 < (g.D:ℝ) := by exact_mod_cast hD
  have wpos : 0 < (g.w:ℝ) := by exact_mod_cast hw
  have xs : x ≤ s.re := hx.trans ha
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have sb : ‖s‖ ≤ K*x := by
    have re := mul_self_le_mul_self (hxp.le.trans xs) hb
    have im := mul_self_le_mul_self (abs_nonneg _) hH
    rw [← sq,sq_abs] at im
    change b^2+H^2 ≤ (K*x)^2 at hrect
    nlinarith [Complex.sq_norm_sub_sq_re s,mul_nonneg hK hxp.le,norm_nonneg s]
  let A (n : ℕ) := ‖(∑ k ∈ Finset.range n,ψ ((k+1:ℕ):ZMod g.Q))-1‖
  let z (i : ℕ) := ∑ b ∈ g.U,(entry i b:ℂ)*ψ (b:ZMod g.Q)
  let F (i : ℕ) : ℝ := if i=0 then 1 else ‖z i‖
  have rep := GRH.centered_prefix_character_unit_rows g.Q ψ hn
  have hz : ∑ a ∈ g.U,ψ (a:ZMod g.Q)=0 := by rw [hU]; exact rep.1
  have hu (b : ℕ) (hb : b∈g.U) : IsUnit (b:ZMod g.Q) := by
    rw [hU] at hb
    exact (ZMod.isUnit_iff_coprime _ _).2 (Finset.mem_filter.mp hb).2
  have corr := GRH.character_weighted_autocorrelation_identity g.Q ψ g.I g.U g.inv
      (fun i => g.W i*g.dual i) entry perm hu
  have he : ((∑ i ∈ g.I,(g.W i*g.dual i:ℕ)*‖z i‖^2:ℝ):ℂ) =
      ∑ k ∈ g.U,(g.T k:ℂ)*ψ (k:ZMod g.Q) := by
    apply corr.symm.trans
    apply Finset.sum_congr rfl
    intro k hk
    rw [hT k hk]
    rfl
  let P := ∑ i ∈ g.I,(g.W i:ℝ)*‖z i‖
  have pm := GRH.character_weighted_moment_abel_inequality g.Q ψ g.I g.U g.inv g.T
     g.W g.scale g.dual z g.L g.c g.rows perm hz hrows hsc he
  have strict : (g.v:ℝ)*P < (budget g:ℝ) := strict_moment g P hL pm htest
  have hrep (r : ℕ) (hr : r<g.Q) (hr0 : r≠0) := hkeys ⟨r,hr⟩ hr0
  have keymem (k : ℕ) : g.key ((k+1)%g.Q) ∈ keys g := by
    by_cases h : (k+1)%g.Q=0
    · simp [h,key0,keys]
    · rcases (hrep _ (Nat.mod_lt _ (NeZero.pos g.Q)) h).1 with eq|mem
      · simp [keys,eq]
      · simp [keys,mem]
  have repr (n : ℕ) : A n=F (g.key (n%g.Q)) := by
    dsimp only [A]
    rw [rep.2 n]
    by_cases h : n%g.Q=0
    · simp [h,key0,F]
    · obtain ⟨km,ent⟩ := hrep _ (Nat.mod_lt _ (NeZero.pos g.Q)) h
      have kn : g.key (n%g.Q) ≠ 0 := by
        rcases km with eq|mem
        · exact eq.trans_ne one_ne_zero
        · exact fun e => hi0 (e ▸ mem)
      rw [if_neg h,show F (g.key (n%g.Q))=‖z (g.key (n%g.Q))‖ from if_neg kn,← hU]
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      rw [ent b hb]
  have group : (∑ k ∈ Finset.range g.M,A (k+1)*(delta g.u k:ℝ))=(g.W 0:ℝ)+P := by
    simp_rw [repr]
    rw [grouped g F keymem hW]
    have e1 : z 1=0 := by simp [z,entry,show ∀ k : ℕ, ¬(1<k ∧ k≤1) from fun _ => by omega]
    rw [keys,Finset.sum_insert (by simp [hi0]),Finset.sum_insert hi1]
    simp only [F,if_pos rfl,mul_one,one_ne_zero,if_false,e1,norm_zero,mul_zero,zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i ≠ 0 := fun e => hi0 (e ▸ hi)
    rw [if_neg hin]
  have tail (n : ℕ) : A n ≤ (g.R:ℝ) := by
    apply (GRH.dirichlet_prefix_unit_count_bound g.Q ψ hn n).trans
    exact_mod_cast (show GRH.DirichletPrefix.weight g.Q n ≤ g.R by
      unfold GRH.DirichletPrefix.weight GRH.DirichletPrefix.weightAt
      split
      · omega
      · rw [Nat.min_def];split <;> omega)
  have est := GRH.dirichlet_abel_bound_of_prefix_envelope g.Q g.M ψ hn s x K (g.R:ℝ) A
      hxp xs ((div_le_iff₀ hxp).2 sb) (Nat.cast_nonneg _) (fun _ => norm_nonneg _) (fun _ => le_rfl) tail
  let E := (∑ k ∈ Finset.range g.M,A (k+1)*(((k:ℝ)+1)^(-x)-((k:ℝ)+2)^(-x)))+
      (g.R:ℝ)*((g.M:ℝ)+1)^(-x)
  have val (k : ℕ) (hk : k ≤ g.M) :
      ((g.u (k+1)-1:ℕ):ℝ) ≤ (g.D:ℝ)*((k:ℝ)+1)^(-x) ∧
      (g.D:ℝ)*((k:ℝ)+1)^(-x) ≤ (g.u (k+1):ℝ) := by
    obtain ⟨_,lo,up,_⟩ := htable ⟨k,by omega⟩
    simpa only [Nat.cast_add,Nat.cast_one] using bracket g.D g.p g.t (k+1) (g.u (k+1)) (by omega) ht lo up
  have term (k : ℕ) (hk : k∈Finset.range g.M) :
      (g.D:ℝ)*(A (k+1)*(((k:ℝ)+1)^(-x)-((k:ℝ)+2)^(-x))) ≤ A (k+1)*(delta g.u k:ℝ) := by
    have hk' := Finset.mem_range.mp hk
    have mono := (htable ⟨k,by omega⟩).2.2.2
    change g.u (k+2) ≤ g.u (k+1) at mono
    rw [delta,Nat.cast_sub ((Nat.sub_le _ _).trans mono)]
    have lo := (val (k+1) (by omega)).1
    simp only [Nat.cast_add,Nat.cast_one] at lo
    rw [show (k:ℝ)+1+1=(k:ℝ)+2 by ring] at lo
    have bd := mul_le_mul_of_nonneg_left (sub_le_sub (val k (by omega)).2 lo)
      (show 0≤A (k+1) from norm_nonneg _)
    linarith only [bd]
  have all : (g.D:ℝ)*E ≤ (g.W 0:ℝ)+P+(g.R:ℝ)*(g.u (g.M+1):ℝ) := by
    rw [← group]
    dsimp only [E]
    rw [mul_add,Finset.mul_sum]
    apply add_le_add (Finset.sum_le_sum term)
    have bd := mul_le_mul_of_nonneg_left (val g.M le_rfl).2 (Nat.cast_nonneg (α:=ℝ) g.R)
    linarith only [bd]
  have hpbud : g.v*(g.W 0+g.R*g.u (g.M+1)) < g.w*g.D := Nat.lt_of_sub_pos hbud
  rw [budget,Nat.cast_sub hpbud.le,Nat.cast_mul,Nat.cast_mul,Nat.cast_add,Nat.cast_mul] at strict
  have upper := mul_le_mul_of_nonneg_left all (Nat.cast_nonneg (α:=ℝ) g.v)
  have final1 : ((g.v:ℝ)*E)*(g.D:ℝ) < (g.w:ℝ)*(g.D:ℝ) := by linarith only [upper,strict]
  have final2 : K*E < 1 := by
    rw [show K*E=((g.v:ℝ)*E)/g.w by dsimp [K];ring,div_lt_one wpos]
    exact (mul_lt_mul_iff_left₀ Dpos).1 final1
  intro hzero
  have lift := DirichletCharacter.LFunction_changeLevel hd χ (s:=s) (.inl hχ)
  rw [hzero,zero_mul] at lift
  have finalBound := est.trans_lt final2
  change ‖(DirichletCharacter.changeLevel hd χ).LFunction s-1‖ < 1 at finalBound
  simp [lift] at finalBound
