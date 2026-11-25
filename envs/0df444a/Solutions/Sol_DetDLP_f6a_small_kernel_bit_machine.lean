-- Prove2me | solution 1 for DetDLP.f6a_small_kernel_bit_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T02:38:18.933107+00:00
-- url     : https://prove2.me/submissions/aff9b102-35e1-4aff-923a-1077ffb5b1c1

import Theorems.Thm_DetDLP_exhaustive_scalar_contraction_leaf_machine
import Theorems.Thm_DetDLP_m14a_separator_edge_budget
import Definitions.Def_DetDLP_FactorBase

open Finset Polynomial DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
set_option autoImplicit false
set_option maxHeartbeats 200000

private theorem budget (c C L₀ h : ℕ) : ∃ K, ∀ X E V d P ell T : ℕ,
    1 ≤ X → E ≤ 3*2^L₀ → V ≤ X^c → d ≤ X → P ≤ X → ell ≤ C*V → T ≤ c*X^c →
    2^E*(8*T+1)*(h*(E+V+d+P+ell+(T+8)+1+1)^h) ≤ K*X^K ∧
    h*(E+V+d+P+ell+(T+8)+1+1)^h ≤ K*X^K := by
  let B := 3*2^L₀
  let F := B+C+c+16
  let k := c+1
  let coeff := 2^B*(8*c+1)*(h*F^h)
  let K := max coeff (k*(h+1))
  refine ⟨K,?_⟩
  intro X E V d P ell T hx he hv hd hp hell ht
  have po : 1 ≤ X^k := Nat.one_le_pow _ _ hx
  have xc : X^c ≤ X^k := Nat.pow_le_pow_right hx (by dsimp [k]; omega)
  have xx : X ≤ X^k := by simpa using (Nat.pow_le_pow_right hx (show 1 ≤ k by dsimp [k]; omega))
  have ve := hv.trans xc
  have ed : E ≤ B*X^k := he.trans (Nat.le_mul_of_pos_right _ po)
  have el := hell.trans (Nat.mul_le_mul_left _ ve)
  have tt := ht.trans (Nat.mul_le_mul_left _ xc)
  have sum : E+V+d+P+ell+(T+8)+1+1 ≤ F*X^k := by
    dsimp [F]; nlinarith [hd.trans xx,hp.trans xx]
  have left : h*(E+V+d+P+ell+(T+8)+1+1)^h ≤ (h*F^h)*(X^k)^h := by
    simpa [mul_pow,mul_assoc] using Nat.mul_le_mul_left h (Nat.pow_le_pow_left sum h)
  have A : 2^E ≤ 2^B := Nat.pow_le_pow_right (by decide) he
  have B' : 8*T+1 ≤ (8*c+1)*X^k := by nlinarith
  have all := Nat.mul_le_mul (Nat.mul_le_mul A B') left
  have eq : 2^B*((8*c+1)*X^k)*(h*F^h*(X^k)^h)=coeff*X^(k*(h+1)) := by
    unfold coeff; rw [pow_mul,pow_succ]; ring
  rw [eq] at all
  have full := all.trans (Nat.mul_le_mul (le_max_left coeff (k*(h+1))) (Nat.pow_le_pow_right hx (le_max_right coeff (k*(h+1)))))
  exact ⟨full,le_trans (Nat.le_mul_of_pos_left _ (by positivity)) full⟩

theorem solution (E : PrimitiveMachine) (out : Fin E.tapeCount) (C c L₀ : ℕ) :
    ∃ (s l K : ℕ) (M : BitProgram.Program 8 (19+(7+s)) l),
      ∀ (G : BipartiteMultigraph) (m k S D P ell : ℕ) (desc : List Bool)
        (A : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→Fin ell→ℕ)
        (spec : LookupSeparatorSpec G m k S D), Nat.clog 2 S < L₀ →
        G.nV ≤ (S+desc.length+1)^c → ell ≤ C*m → 0<P → P≤S → 0<ell →
        (∀ v t i,A v t i<2^P) →
        (∀ v t,RunsWithin E out (encodePortQuery desc v.val (List.ofFn t))
          (encodeNatListBin (List.ofFn (A v t))) (polyBound c (S+desc.length)) (polyBound c (S+desc.length))) →
        let w := G.nE+G.nV*(P+Nat.clog 2 ell)+1+P
        let r := G.nV+3
        let pairs := (List.finRange G.nE).map fun e => ((G.endpoints e).1.val,(G.endpoints e).2.val)
        let code := Nat.ofDigits r (pairs.flatMap fun xy => [xy.1,xy.2])+r^(2*pairs.length)
        let frame := Fin.addCases (m:=8) (n:=11) (fun _ => ([]:List Bool))
          (fun j => ((![2^G.nE,G.nV,0,0,1,0,0,0,1,1,2^G.nE] : Fin 11→ℕ) j).bits)
        let metadata : Fin 7→List Bool := ![desc,r.bits,code.bits,(code/r).bits,(2^w-1).bits,(2^w).bits,(2^w-1-2).bits]
        let input := Fin.addCases frame (Fin.addCases metadata (fun _ : Fin s => ([]:List Bool)))
        let cap := K*(S+desc.length+1)^K
        let Z := BTNContract G (fun v t => ∑ i : Fin ell,monomial i.val (A v t i:ℤ))
        ∀ reg : Fin 8→Bool,
        let start : BitProgram.Cfg 8 (19+(7+s)) l := ⟨some M.entry,reg,input⟩
        ∃ (z steps : ℕ) (rf : Fin 8→Bool) (o : Fin (19+(7+s))→List Bool),steps ≤ cap ∧
          BitProgram.Trace M steps start ⟨none,rf,o⟩ ∧
          (∀ j c,j ≤ steps → BitProgram.Trace M j start c → ∀ i,(c.stacks i).length ≤ cap) ∧
          o ((13:Fin 19).castAdd (7+s))=z.bits ∧
          encodeNatListBin (List.ofFn fun i : Fin ell => z/(2^w)^i.val%(2^w)%(2^P))=
          encodeNatListBin (List.ofFn fun i : Fin ell => (Z.coeff i.val:ZMod (2^P)).val) := by
  obtain ⟨s,l,h,M,ker⟩ := exhaustive_scalar_contraction_leaf_machine E out
  obtain ⟨K,cap⟩ := budget c C L₀ h
  refine ⟨s,l,K,M,?_⟩
  intro G m k S D P ell desc A spec small verts arity hp hP hel coeff run
  let baseSize := S+desc.length+1
  let T := c*baseSize^c
  have bound : (T:ℝ) = polyBound c (S+desc.length) := by simp [T,baseSize,polyBound]
  have call := ker G P ell desc A T T hp hel coeff (by simpa only [bound] using run)
  have se := (Nat.clog_le_iff_le_pow (by decide : 1<2)).mp small.le
  have edges := (m14a_separator_edge_budget spec).2.trans (Nat.mul_le_mul_left _ se)
  have nv := spec.lookupVerts.card_le_univ
  rw [spec.card_lookup,Fintype.card_fin] at nv
  have hX : 1 ≤ baseSize := by dsimp [baseSize]; omega
  have hd : desc.length ≤ baseSize := by dsimp [baseSize]; omega
  have hPX : P ≤ baseSize := by dsimp [baseSize]; omega
  have hV : m ≤ G.nV := by omega
  have bounds := cap baseSize G.nE G.nV desc.length P ell T hX edges verts hd hPX
    (arity.trans (Nat.mul_le_mul_left C hV)) le_rfl
  intro w r pairs code frame metadata input limit Z reg start
  obtain ⟨z,n,rf,o,hn,tr,sz,output,eq⟩ := call reg
  exact ⟨z,n,rf,o,hn.trans bounds.1,tr,fun j b hj hb i => (sz j b hj hb i).trans bounds.2,output,eq⟩
